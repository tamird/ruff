use indexmap::map::Entry;
use ruff_python_ast::{self as ast, name::Name};
use ruff_text_size::{Ranged, TextRange};
use rustc_hash::FxHashSet;
use ty_python_core::scope::ScopeId;
use ty_python_core::semantic_index;

use crate::reachability::ReachabilityEvaluationCache;
use crate::types::call::collect_keyword_items;
use crate::types::set_theoretic::UnionBuilder;
use crate::types::typed_dict::{
    UnpackedTypedDict, UnpackedTypedDictKey, extract_unpacked_typed_dict_from_value_type,
};
use crate::types::{KnownClass, ProgramEnvironment, Type, UnionType};
use crate::{Db, FxIndexMap};

pub(crate) mod contents;

/// Publication of contents evidence. An impossible mapping is not an empty mapping, and
/// must not fall back to the receiver's ordinary type when matching a keyword argument.
#[derive(Clone, Copy)]
pub(crate) enum DictionaryFallback {
    Unavailable,
    Unreachable,
}

pub(crate) type DictionaryObservation<'db> = Result<DictionaryItems<'db>, DictionaryFallback>;

/// A named value or per-name residual restriction in a dictionary argument.
#[derive(Clone, Debug, PartialEq, Eq, get_size2::GetSize, salsa::SalsaValue)]
pub struct DictionaryItem<'db> {
    pub name: Name,
    pub ty: Type<'db>,
    pub kind: DictionaryItemKind,
    /// The key's definition or unpacking expression in the call's file.
    pub source: TextRange,
}

/// A dictionary entry's presence and named-value evidence.
#[derive(Clone, Copy, Debug, PartialEq, Eq, get_size2::GetSize, salsa::SalsaValue)]
pub enum DictionaryItemKind {
    /// A named value is present on every path.
    Required,
    /// A named value may be present.
    Optional,
    /// A restriction on values supplied by unknown keys, not evidence of a named value.
    /// `Never` excludes this name from the residual.
    Residual,
}

impl DictionaryItemKind {
    pub(crate) fn from_required<'db>(db: &'db dyn Db, ty: Type<'db>, is_required: bool) -> Self {
        if is_required {
            Self::Required
        } else if ty.resolve_type_alias(db).is_never() {
            Self::Residual
        } else {
            Self::Optional
        }
    }

    pub(crate) const fn is_required(self) -> bool {
        matches!(self, Self::Required)
    }
}

impl DictionaryItem<'_> {
    pub const fn is_required(&self) -> bool {
        let Self {
            name: _,
            ty: _,
            kind,
            source: _,
        } = self;
        kind.is_required()
    }
}

/// Dictionary entries available at a call argument.
#[derive(Clone, Debug, PartialEq, Eq, get_size2::GetSize, salsa::SalsaValue)]
pub struct DictionaryItems<'db> {
    pub items: Box<[DictionaryItem<'db>]>,
    pub extra_items: DictionaryExtraItems<'db>,
}

/// Evidence about dictionary values beyond the named entries.
#[derive(Clone, Copy, Debug, PartialEq, Eq, get_size2::GetSize, salsa::SalsaValue)]
pub enum DictionaryExtraItems<'db> {
    /// Every possible key has an entry, which records its own evidence.
    Closed,
    /// Values for additional keys. Every represented name is excluded; its entry records the
    /// applicable value restriction and whether a named value can supply it.
    Value(Type<'db>),
}

impl<'db> DictionaryItems<'db> {
    /// Whether the named entries account for every possible key.
    pub const fn is_complete(&self) -> bool {
        matches!(self.extra_items, DictionaryExtraItems::Closed)
    }

    pub(crate) fn observed(
        db: &'db dyn Db,
        scope: ScopeId<'db>,
        expression: &ast::Expr,
        argument_type: Type<'db>,
        reachability: &ReachabilityEvaluationCache<'db>,
    ) -> DictionaryObservation<'db> {
        contents::at_use(db, scope, expression, argument_type, reachability)
    }

    pub(crate) fn expression(
        db: &'db dyn Db,
        env: &ProgramEnvironment<'db>,
        scope: ScopeId<'db>,
        expression: &ast::Expr,
        expression_type: &mut impl FnMut(&ast::Expr) -> Option<Type<'db>>,
    ) -> DictionaryObservation<'db> {
        match expression {
            ast::Expr::Dict(_) => Self::literal(db, env, scope, expression, expression_type),
            ast::Expr::DictComp(comprehension) => {
                let ast::ExprDictComp {
                    node_index: _,
                    range: _,
                    key,
                    value,
                    generators: _,
                } = comprehension;
                let key = key.as_deref().ok_or(DictionaryFallback::Unavailable)?;
                let key_ty = expression_type(key).ok_or(DictionaryFallback::Unavailable)?;
                let value_ty = expression_type(value).ok_or(DictionaryFallback::Unavailable)?;
                let resolved_value = value_ty.resolve_type_alias(db);
                if resolved_value.is_never() || resolved_value.is_divergent() {
                    // A bottom body can be skipped by an empty iterator or a filter. It does not
                    // establish either an unreachable comprehension or a supplied keyword.
                    return Err(DictionaryFallback::Unavailable);
                }
                let key_ty = UnionBuilder::new(db, env).add(key_ty).build();
                let keys = match &key_ty {
                    Type::Union(union) => union.elements(db),
                    ty => std::slice::from_ref(ty),
                };
                let items = keys
                    .iter()
                    .map(|ty| {
                        let name = ty
                            .string_literal_value(db)
                            .ok_or(DictionaryFallback::Unavailable)?;
                        Ok(DictionaryItem {
                            name: Name::new(name),
                            ty: value_ty,
                            // Iteration and filtering need not supply any particular key.
                            kind: DictionaryItemKind::Residual,
                            source: key.range(),
                        })
                    })
                    .collect::<Result<_, DictionaryFallback>>()?;
                Ok(Self {
                    items,
                    extra_items: DictionaryExtraItems::Closed,
                })
            }
            ast::Expr::Call(call) => {
                let ast::ExprCall {
                    node_index: _,
                    range_start: _,
                    func,
                    arguments,
                } = call;
                let Type::ClassLiteral(class) =
                    expression_type(func).ok_or(DictionaryFallback::Unavailable)?
                else {
                    return Err(DictionaryFallback::Unavailable);
                };
                if !class.is_known(db, KnownClass::Dict) {
                    return Err(DictionaryFallback::Unavailable);
                }
                let mut dictionary = DictionaryItemsBuilder::default();
                match arguments.args.as_ref() {
                    [] => {}
                    [source] => {
                        if source.is_starred_expr() {
                            return Err(DictionaryFallback::Unavailable);
                        }
                        let source = Self::positional_source(
                            db,
                            env,
                            scope,
                            expression.into(),
                            source,
                            expression_type,
                        )?;
                        dictionary.overlay(db, env, source);
                    }
                    _ => return Err(DictionaryFallback::Unavailable),
                }
                let keywords =
                    Self::keywords(db, env, scope, &arguments.keywords, expression_type)?;
                dictionary.overlay(db, env, keywords);
                Ok(dictionary.finish())
            }
            _ => Err(DictionaryFallback::Unavailable),
        }
    }

    fn keywords(
        db: &'db dyn Db,
        env: &ProgramEnvironment<'db>,
        scope: ScopeId<'db>,
        keywords: &[ast::Keyword],
        expression_type: &mut impl FnMut(&ast::Expr) -> Option<Type<'db>>,
    ) -> DictionaryObservation<'db> {
        collect_keyword_items(
            db,
            env,
            keywords.iter().map(|keyword| {
                let ast::Keyword {
                    node_index: _,
                    range: _,
                    arg,
                    value,
                } = keyword;
                if let Some(name) = arg {
                    let ty = expression_type(value).ok_or(DictionaryFallback::Unavailable)?;
                    Ok(Self {
                        items: Box::new([DictionaryItem {
                            name: name.id.clone(),
                            ty,
                            kind: DictionaryItemKind::Required,
                            source: name.range(),
                        }]),
                        extra_items: DictionaryExtraItems::Closed,
                    })
                } else {
                    Self::unpacked_expression(db, env, scope, value, expression_type)
                }
            }),
        )
    }

    fn unpacked_expression(
        db: &'db dyn Db,
        env: &ProgramEnvironment<'db>,
        scope: ScopeId<'db>,
        expression: &ast::Expr,
        expression_type: &mut impl FnMut(&ast::Expr) -> Option<Type<'db>>,
    ) -> DictionaryObservation<'db> {
        let observed = Self::expression(db, env, scope, expression, expression_type);
        if expression.is_dict_expr() || !matches!(observed, Err(DictionaryFallback::Unavailable)) {
            // Unsupported literals decline atomically; unreachable operands stay unreachable.
            return observed;
        }
        let ty = expression_type(expression).ok_or(DictionaryFallback::Unavailable)?;
        let index = semantic_index(db, scope.program_file(db));
        let cache = ReachabilityEvaluationCache::new(
            scope,
            index
                .use_def_map(scope.file_scope_id(db))
                .reachability_constraints(),
        );
        match contents::at_use(db, scope, expression, ty, &cache) {
            Err(DictionaryFallback::Unavailable) => Self::unpacked(db, env, ty, expression.range())
                .ok_or(DictionaryFallback::Unavailable),
            observed => observed,
        }
    }

    fn positional_source(
        db: &'db dyn Db,
        env: &ProgramEnvironment<'db>,
        scope: ScopeId<'db>,
        call: ast::ExprRef<'_>,
        source: &ast::Expr,
        expression_type: &mut impl FnMut(&ast::Expr) -> Option<Type<'db>>,
    ) -> DictionaryObservation<'db> {
        if ty_python_core::place::PlaceExpr::try_from_expr(source).is_none() {
            return Self::unpacked_expression(db, env, scope, source, expression_type);
        }
        let ty = expression_type(source).ok_or(DictionaryFallback::Unavailable)?;
        let index = semantic_index(db, scope.program_file(db));
        let cache = ReachabilityEvaluationCache::new(
            scope,
            index
                .use_def_map(scope.file_scope_id(db))
                .reachability_constraints(),
        );
        match contents::at_snapshot(db, scope, source, call, ty, &cache) {
            Err(DictionaryFallback::Unavailable) => {
                Self::unpacked(db, env, ty, source.range()).ok_or(DictionaryFallback::Unavailable)
            }
            observed => observed,
        }
    }

    fn literal(
        db: &'db dyn Db,
        env: &ProgramEnvironment<'db>,
        scope: ScopeId<'db>,
        expression: &ast::Expr,
        expression_type: &mut impl FnMut(&ast::Expr) -> Option<Type<'db>>,
    ) -> DictionaryObservation<'db> {
        let ast::Expr::Dict(ast::ExprDict {
            node_index: _,
            range: _,
            items,
        }) = expression
        else {
            return Err(DictionaryFallback::Unavailable);
        };
        let mut dictionary = DictionaryItemsBuilder::default();
        for ast::DictItem { key, value } in items {
            let Some(key) = key else {
                let unpacked = Self::unpacked_expression(db, env, scope, value, expression_type)?;
                dictionary.overlay(db, env, unpacked);
                continue;
            };
            let name = match key {
                ast::Expr::StringLiteral(literal) => Name::new(literal.value.to_str()),
                _ => {
                    let ty = expression_type(key).ok_or(DictionaryFallback::Unavailable)?;
                    let name = ty
                        .string_literal_value(db)
                        .ok_or(DictionaryFallback::Unavailable)?;
                    Name::new(name)
                }
            };
            let ty = expression_type(value).ok_or(DictionaryFallback::Unavailable)?;
            let entry = DictionaryItem {
                name: name.clone(),
                ty,
                kind: DictionaryItemKind::Required,
                source: key.range(),
            };
            // Repeated keys replace their values without changing insertion order.
            dictionary.items.insert(name, entry);
        }
        Ok(dictionary.finish())
    }

    /// Read an unpacked source's existing type without inferring its expression again.
    fn unpacked(
        db: &'db dyn Db,
        env: &ProgramEnvironment<'db>,
        ty: Type<'db>,
        source: TextRange,
    ) -> Option<Self> {
        // An unreachable source is not evidence for an inhabited, empty mapping.
        if ty.resolve_type_alias(db).is_never() {
            return None;
        }
        if let Some(unpacked) = extract_unpacked_typed_dict_from_value_type(db, env, ty) {
            let UnpackedTypedDict {
                keys,
                openness,
                has_implicit_extra_items,
            } = unpacked;
            // Hidden TypedDict fields follow a different call policy from ordinary mapping
            // values. Preserve the existing literal inference until that provenance is retained.
            if has_implicit_extra_items {
                return None;
            }
            return Some(Self {
                items: keys
                    .into_iter()
                    .map(|(name, key)| {
                        let UnpackedTypedDictKey {
                            value_ty,
                            kind,
                            definition: _,
                        } = key;
                        DictionaryItem {
                            name,
                            ty: value_ty,
                            kind,
                            source,
                        }
                    })
                    .collect(),
                extra_items: openness
                    .effective_extra_items()
                    .map_or(DictionaryExtraItems::Closed, |extra| {
                        DictionaryExtraItems::Value(extra.declared_ty)
                    }),
            });
        }
        let (key_ty, value_ty) = ty.unpack_keys_and_items(db, env)?;
        let str_ty = KnownClass::Str.to_instance(db, env);
        if key_ty.is_assignable_to(db, env, str_ty) && !str_ty.is_assignable_to(db, env, key_ty) {
            // The ordinary mapping checker handles key domains that exclude some strings.
            // A homogeneous residual would incorrectly apply their values to other names.
            // Non-string keys retain the call checker's separate key-type diagnostic.
            return None;
        }
        Some(Self {
            items: Box::default(),
            extra_items: if value_ty.resolve_type_alias(db).is_never() {
                DictionaryExtraItems::Closed
            } else {
                DictionaryExtraItems::Value(value_ty)
            },
        })
    }
}

/// An ordered overlay of mapping sources. The residual excludes every represented name.
#[derive(Default)]
struct DictionaryItemsBuilder<'db> {
    items: FxIndexMap<Name, DictionaryItem<'db>>,
    extra_items: Option<Type<'db>>,
}

impl<'db> DictionaryItemsBuilder<'db> {
    fn overlay(
        &mut self,
        db: &'db dyn Db,
        env: &ProgramEnvironment<'db>,
        dictionary: DictionaryItems<'db>,
    ) {
        let DictionaryItems { items, extra_items } = dictionary;
        let incoming_extra = match extra_items {
            DictionaryExtraItems::Closed => None,
            DictionaryExtraItems::Value(ty) => Some(ty),
        };
        if let Some(ty) = incoming_extra {
            let names: FxHashSet<_> = items.iter().map(|item| item.name.clone()).collect();
            for item in self.items.values_mut() {
                if !names.contains(&item.name) {
                    item.ty = UnionType::from_two_elements(db, env, item.ty, ty);
                }
            }
        }
        for mut item in items {
            match self.items.entry(item.name.clone()) {
                Entry::Occupied(mut entry) => {
                    if !item.is_required() {
                        let previous = entry.get();
                        item.ty = UnionType::from_two_elements(db, env, previous.ty, item.ty);
                        if item.kind == DictionaryItemKind::Residual {
                            item.source = previous.source;
                        }
                        item.kind = match previous.kind {
                            DictionaryItemKind::Required => DictionaryItemKind::Required,
                            DictionaryItemKind::Optional => DictionaryItemKind::Optional,
                            DictionaryItemKind::Residual => item.kind,
                        };
                    }
                    entry.insert(item);
                }
                Entry::Vacant(entry) => {
                    if !item.is_required()
                        && let Some(ty) = self.extra_items
                    {
                        item.ty = UnionType::from_two_elements(db, env, ty, item.ty);
                    }
                    entry.insert(item);
                }
            }
        }
        if let Some(ty) = incoming_extra {
            self.extra_items = Some(self.extra_items.map_or(ty, |previous| {
                UnionType::from_two_elements(db, env, previous, ty)
            }));
        }
    }

    fn finish(self) -> DictionaryItems<'db> {
        let Self { items, extra_items } = self;
        DictionaryItems {
            items: items.into_values().collect(),
            extra_items: extra_items
                .map_or(DictionaryExtraItems::Closed, DictionaryExtraItems::Value),
        }
    }
}
