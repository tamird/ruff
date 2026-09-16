use ruff_db::diagnostic::Span;
use ruff_python_ast::{self as ast, name::Name};
use ruff_text_size::Ranged;
use ty_python_core::starlark::{
    StarlarkAvailability, StarlarkGlobalDeclaration, StarlarkGlobalKind, StarlarkModuleRole,
};

use super::TypeInferenceBuilder;
use crate::types::class::{
    ClassLiteral, DynamicClassAnchor, DynamicClassLiteral, SynthesizedClass, SynthesizedField,
};
use crate::types::diagnostic::{INVALID_ARGUMENT_TYPE, UNAVAILABLE_HOST_FUNCTION};
use crate::types::infer::InferenceRegion;
use crate::types::starlark::{StarlarkField, StarlarkGlobal};
use crate::types::{KnownInstanceType, SubclassOfType, Type};

impl<'db> TypeInferenceBuilder<'db, '_> {
    pub(super) fn check_starlark_availability(&self, callee: &ast::Expr, callable: Type<'db>) {
        let db = self.db();
        let global = match callable {
            Type::KnownInstance(KnownInstanceType::StarlarkGlobal(global)) => global,
            Type::Union(union) => {
                for element in union.elements(db) {
                    self.check_starlark_availability(callee, *element);
                }
                return;
            }
            Type::TypeAlias(alias) => {
                self.check_starlark_availability(callee, alias.value_type(db));
                return;
            }
            _ => return,
        };
        let Some(module) = self.program_file().starlark_module(db) else {
            return;
        };
        let Some(declaration) = global.declaration(db) else {
            return;
        };
        let StarlarkGlobalDeclaration { name, kind } = declaration;
        let StarlarkGlobalKind::Native {
            parameters: _,
            return_type: _,
            availability,
        } = kind
        else {
            return;
        };
        if *availability == StarlarkAvailability::LoadedModuleInitialization
            && module.role(db) == StarlarkModuleRole::Root
            && let Some(builder) = self.context.report_lint(&UNAVAILABLE_HOST_FUNCTION, callee)
        {
            builder.into_diagnostic(format_args!("`{name}` is unavailable from the source root"));
        }
    }

    /// Refines an intrinsic's result after normal call binding and argument inference.
    pub(super) fn infer_starlark_call_result(
        &mut self,
        call: &ast::ExprCall,
        global: StarlarkGlobal<'db>,
    ) -> Option<Type<'db>> {
        let db = self.db();
        let declaration = global.declaration(db)?;
        let StarlarkGlobalDeclaration { name: _, kind } = declaration;
        match kind {
            StarlarkGlobalKind::Native {
                parameters: _,
                return_type: _,
                availability: _,
            } => None,
            StarlarkGlobalKind::Field => Some(self.infer_starlark_field(call)),
            StarlarkGlobalKind::Record => Some(self.infer_starlark_class(call, true)),
            StarlarkGlobalKind::RecordWithValidator => Some(self.infer_starlark_class(call, true)),
            StarlarkGlobalKind::Struct => Some(self.infer_starlark_class(call, false)),
        }
    }

    fn infer_starlark_field(&mut self, call: &ast::ExprCall) -> Type<'db> {
        if call.arguments.args.iter().any(ast::Expr::is_starred_expr)
            || call
                .arguments
                .keywords
                .iter()
                .any(|keyword| keyword.arg.is_none())
        {
            return Type::unknown();
        }
        let Some(annotation) = call.arguments.args.first() else {
            return Type::unknown();
        };
        let annotation_ty = self
            .infer_name_or_attribute_type_expression(self.expression_type(annotation), annotation);
        let default = call.arguments.args.get(1).or_else(|| {
            call.arguments
                .keywords
                .iter()
                .find(|keyword| keyword.arg.as_deref() == Some("default"))
                .map(|keyword| &keyword.value)
        });
        let default_type = default.map(|default| self.expression_type(default));
        if let Some(default) = default
            && let Some(default_type) = default_type
            && !default_type.is_assignable_to(self.db(), self.program_environment(), annotation_ty)
            && let Some(builder) = self.context.report_lint(&INVALID_ARGUMENT_TYPE, default)
        {
            let mut diagnostic =
                builder.into_diagnostic("Default value is incompatible with the field type");
            diagnostic.set_primary_annotation_message(format_args!(
                "Expected `{}`, found `{}`",
                annotation_ty.display(self.db(), self.program_environment()),
                default_type.display(self.db(), self.program_environment())
            ));
            diagnostic.annotate(
                self.context
                    .secondary(annotation)
                    .message("Field type declared here"),
            );
        }
        Type::KnownInstance(KnownInstanceType::StarlarkField(StarlarkField::new(
            self.db(),
            annotation_ty,
            default_type,
            Span::from(self.file()).with_range(annotation.range()),
        )))
    }

    fn infer_starlark_class(
        &mut self,
        call: &ast::ExprCall,
        keyword_constructor: bool,
    ) -> Type<'db> {
        if call
            .arguments
            .keywords
            .iter()
            .any(|keyword| keyword.arg.is_none())
        {
            return if keyword_constructor {
                SubclassOfType::subclass_of_unknown()
            } else {
                Type::unknown()
            };
        }
        let mut fields = Vec::with_capacity(call.arguments.keywords.len());
        for keyword in &call.arguments.keywords {
            let Some(name) = &keyword.arg else {
                continue;
            };
            let value = self.expression_type(&keyword.value);
            let (ty, default, origin) = if keyword_constructor {
                match value {
                    Type::KnownInstance(KnownInstanceType::StarlarkField(field)) => (
                        field.annotation(self.db()),
                        field.default(self.db()),
                        field.origin(self.db()).clone(),
                    ),
                    _ => (
                        self.infer_name_or_attribute_type_expression(value, &keyword.value),
                        None,
                        Span::from(self.file()).with_range(keyword.value.range()),
                    ),
                }
            } else {
                (
                    value,
                    None,
                    Span::from(self.file()).with_range(keyword.value.range()),
                )
            };
            fields.push(SynthesizedField {
                name: name.id.clone(),
                ty,
                default,
                origin,
            });
        }

        // A simple assigned declaration gets the same identity and navigation
        // anchor as other dynamic classes. Nested calls use their scope offset.
        let definition = match self.region {
            InferenceRegion::Definition(definition) => definition
                .kind(self.db())
                .value(self.module())
                .filter(|value| value.range() == call.range())
                .map(|_| definition),
            _ => None,
        };
        let name = definition
            .and_then(|definition| definition.name(self.db()))
            .map(Name::new)
            .unwrap_or_else(|| {
                Name::new(if keyword_constructor {
                    "record"
                } else {
                    "struct"
                })
            });
        let anchor = match definition {
            Some(definition) => DynamicClassAnchor::Definition(definition),
            None => DynamicClassAnchor::ScopeOffset {
                scope: self.scope(),
                offset: self.dynamic_class_scope_offset(call),
                explicit_bases: Box::default(),
            },
        };
        let class = DynamicClassLiteral::new(
            self.db(),
            name,
            anchor,
            Box::default(),
            false,
            None,
            Some(SynthesizedClass {
                fields: fields.into_boxed_slice(),
                keyword_constructor,
            }),
        );
        if keyword_constructor {
            Type::ClassLiteral(ClassLiteral::Dynamic(class))
        } else {
            ClassLiteral::Dynamic(class)
                .to_non_generic_instance(self.db(), self.program_environment())
        }
    }
}
