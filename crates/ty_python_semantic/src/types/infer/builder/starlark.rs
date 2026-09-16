use ruff_python_ast as ast;
use ty_python_core::starlark::{
    StarlarkAvailability, StarlarkGlobalDeclaration, StarlarkGlobalKind, StarlarkModuleRole,
};

use super::TypeInferenceBuilder;
use crate::types::diagnostic::UNAVAILABLE_HOST_FUNCTION;
use crate::types::{KnownInstanceType, Type};

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
        } = kind;
        if *availability == StarlarkAvailability::LoadedModuleInitialization
            && module.role(db) == StarlarkModuleRole::Root
            && let Some(builder) = self.context.report_lint(&UNAVAILABLE_HOST_FUNCTION, callee)
        {
            builder.into_diagnostic(format_args!("`{name}` is unavailable from the source root"));
        }
    }
}
