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
use crate::types::{KnownClass, MemberLookupPolicy, ProgramEnvironment, Type, UnionType};
use crate::{Db, FxIndexMap};

pub(crate) mod contents;
pub(crate) mod records;

/// The first value of an immediately indexed builtin dictionary snapshot.
pub(crate) fn first_value<'db>(
    db: &'db dyn Db,
    env: &ProgramEnvironment<'db>,
    scope: ScopeId<'db>,
    subscript: &ast::ExprSubscript,
    reachability: &ReachabilityEvaluationCache<'db>,
    expression_type: impl FnMut(&ast::Expr) -> Option<Type<'db>>,
) -> Option<Type<'db>> {
    let (_, first_entry) =
        first_value_read(db, env, scope, subscript, reachability, expression_type)?;
    match first_entry {
        DictionaryFirstEntry::Entry { key: _, value } => Some(value),
        DictionaryFirstEntry::Unknown => None,
        DictionaryFirstEntry::Empty => None,
    }
}

pub(crate) fn first_value_read<'ast, 'db>(
    db: &'db dyn Db,
    env: &ProgramEnvironment<'db>,
    scope: ScopeId<'db>,
    subscript: &'ast ast::ExprSubscript,
    reachability: &ReachabilityEvaluationCache<'db>,
    mut expression_type: impl FnMut(&ast::Expr) -> Option<Type<'db>>,
) -> Option<(
    ty_python_core::place::DictionaryFirstValueRead<'ast>,
    DictionaryFirstEntry<'db>,
)> {
    let read = ty_python_core::place::DictionaryFirstValueRead::from_subscript(subscript)?;
    if let Some(list) = read.list {
        let Type::ClassLiteral(class) = expression_type(&list.func)? else {
            return None;
        };
        if !class.is_known(db, KnownClass::List) {
            return None;
        }
    } else {
        let Type::NominalInstance(result) = expression_type(&subscript.value)? else {
            return None;
        };
        if !result.has_known_class(db, KnownClass::List) {
            return None;
        }
    }
    let Type::BoundMethod(method) = expression_type(&read.values.func)? else {
        return None;
    };
    let declared = KnownClass::Dict
        .to_instance(db, env)
        .member_lookup_with_policy(db, env, "values", MemberLookupPolicy::NO_INSTANCE_FALLBACK)
        .place
        .ignore_possibly_undefined()?;
    let Type::BoundMethod(declared) = declared else {
        return None;
    };
    if method.function(db)?.definition(db) != declared.function(db)?.definition(db) {
        return None;
    }
    let receiver_type = expression_type(read.receiver)?;
    let contents::ContentsValue::Mapping(mapping) = contents::snapshot_contents(
        db,
        scope,
        read.receiver,
        read.receiver.into(),
        receiver_type,
        reachability,
    ) else {
        return None;
    };
    if !mapping.builtin {
        return None;
    }
    Some((read, mapping.dictionary.first_entry))
}

/// The nominal type is `dict`; runtime subclasses can still override its operations.
pub(crate) fn has_dict_type<'db>(
    db: &'db dyn Db,
    env: &ProgramEnvironment<'db>,
    ty: Type<'db>,
) -> bool {
    let is_instance = |ty: Type<'_>| {
        ty.as_nominal_instance().is_some_and(|instance| {
            instance.has_known_class(db, KnownClass::Dict)
                || KnownClass::Dict.allocation_class(db, env)
                    == Some(instance.class_literal(db, env))
        })
    };
    match ty {
        Type::Union(union) => union.elements(db).iter().copied().all(is_instance),
        _ => is_instance(ty),
    }
}

/// Observe a nominal-dictionary item through the existing contents history.
/// Closed `TypedDict` schemas are excluded: exposure can preserve their required entries.
fn observed_item_type<'db>(
    db: &'db dyn Db,
    scope: ScopeId<'db>,
    subscript: &ast::ExprSubscript,
    receiver_type: Type<'db>,
    reachability: &ReachabilityEvaluationCache<'db>,
) -> Option<(Type<'db>, DictionaryItemKind)> {
    if !has_dict_type(db, &ProgramEnvironment::from_scope(scope), receiver_type) {
        return None;
    }
    let key = subscript.slice.as_string_literal_expr()?.value.to_str();
    let dictionary =
        match DictionaryItems::observed(db, scope, &subscript.value, receiver_type, reachability) {
            Ok(dictionary) => dictionary,
            Err(fallback) => match fallback {
                DictionaryFallback::Unavailable => return None,
                DictionaryFallback::Unreachable => {
                    return Some((Type::Never, DictionaryItemKind::Required));
                }
            },
        };
    dictionary
        .items
        .iter()
        .find(|item| item.name == key)
        .map(|item| (item.ty, item.kind))
}

pub(crate) fn required_item_type<'db>(
    db: &'db dyn Db,
    scope: ScopeId<'db>,
    subscript: &ast::ExprSubscript,
    receiver_type: Type<'db>,
    reachability: &ReachabilityEvaluationCache<'db>,
) -> Option<Type<'db>> {
    let (ty, kind) = observed_item_type(db, scope, subscript, receiver_type, reachability)?;
    kind.is_required().then_some(ty)
}

pub(crate) fn proved_item_type<'db>(
    db: &'db dyn Db,
    scope: ScopeId<'db>,
    subscript: &ast::ExprSubscript,
    receiver_type: Type<'db>,
    reachability: &ReachabilityEvaluationCache<'db>,
) -> Option<Type<'db>> {
    let (ty, kind) = observed_item_type(db, scope, subscript, receiver_type, reachability)?;
    (kind.is_required() || contents::has_confined_origin(db, scope, &subscript.value)).then_some(ty)
}

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
    /// Insertion-order evidence at this observation's snapshot, independent of `items` order.
    pub first_entry: DictionaryFirstEntry<'db>,
}

/// Evidence about the first entry of a runtime dictionary.
#[derive(Clone, Debug, PartialEq, Eq, get_size2::GetSize, salsa::SalsaValue)]
pub enum DictionaryFirstEntry<'db> {
    /// Neither emptiness nor the first entry is known.
    Unknown,
    Empty,
    /// The dictionary is nonempty. Only exact string keys have a recorded name.
    Entry {
        key: Option<Name>,
        value: Type<'db>,
    },
}

impl<'db> DictionaryFirstEntry<'db> {
    fn set(
        &mut self,
        db: &'db dyn Db,
        env: &ProgramEnvironment<'db>,
        name: Option<&str>,
        ty: Type<'db>,
    ) {
        match self {
            Self::Unknown => {}
            Self::Empty => {
                *self = Self::Entry {
                    key: name.map(Name::new),
                    value: ty,
                };
            }
            Self::Entry { key, value } => {
                if let Some(key) = key.as_ref()
                    && let Some(name) = name
                {
                    if key == name {
                        *value = ty;
                    }
                } else {
                    *value = UnionType::from_two_elements(db, env, *value, ty);
                }
            }
        }
    }

    fn join(&self, db: &'db dyn Db, env: &ProgramEnvironment<'db>, other: &Self) -> Self {
        match (self, other) {
            (Self::Empty, Self::Empty) => Self::Empty,
            (
                Self::Entry { key, value },
                Self::Entry {
                    key: other_key,
                    value: other_value,
                },
            ) => Self::Entry {
                key: if key == other_key { key.clone() } else { None },
                value: UnionType::from_two_elements(db, env, *value, *other_value),
            },
            _ => Self::Unknown,
        }
    }
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
            ast::Expr::BinOp(binary) => {
                let ast::ExprBinOp {
                    node_index: _,
                    range: _,
                    left,
                    op,
                    right,
                } = binary;
                if *op != ast::Operator::BitOr {
                    return Err(DictionaryFallback::Unavailable);
                }
                let mut dictionary = DictionaryItemsBuilder::default();
                for operand in [left.as_ref(), right.as_ref()] {
                    let source = Self::builtin_source(
                        db,
                        env,
                        scope,
                        expression.into(),
                        operand,
                        expression_type,
                    )?;
                    dictionary.overlay(db, env, source);
                }
                Ok(dictionary.finish())
            }
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
                    first_entry: DictionaryFirstEntry::Unknown,
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
                        first_entry: DictionaryFirstEntry::Entry {
                            key: Some(name.id.clone()),
                            value: ty,
                        },
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
        Self::unpacked_value(db, env, scope, expression, expression_type)
    }

    fn unpacked_value(
        db: &'db dyn Db,
        env: &ProgramEnvironment<'db>,
        scope: ScopeId<'db>,
        expression: &ast::Expr,
        expression_type: &mut impl FnMut(&ast::Expr) -> Option<Type<'db>>,
    ) -> DictionaryObservation<'db> {
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
        snapshot: ast::ExprRef<'_>,
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
        match contents::at_snapshot(db, scope, source, snapshot, ty, &cache) {
            Err(DictionaryFallback::Unavailable) => {
                Self::unpacked(db, env, ty, source.range()).ok_or(DictionaryFallback::Unavailable)
            }
            observed => observed,
        }
    }

    /// Union dispatch requires a builtin allocation, not just a nominal dictionary type.
    pub(super) fn builtin_source(
        db: &'db dyn Db,
        env: &ProgramEnvironment<'db>,
        scope: ScopeId<'db>,
        snapshot: ast::ExprRef<'_>,
        source: &ast::Expr,
        expression_type: &mut impl FnMut(&ast::Expr) -> Option<Type<'db>>,
    ) -> DictionaryObservation<'db> {
        if ty_python_core::place::PlaceExpr::try_from_expr(source).is_none() {
            return Self::expression(db, env, scope, source, expression_type);
        }
        let ty = expression_type(source).ok_or(DictionaryFallback::Unavailable)?;
        let index = semantic_index(db, scope.program_file(db));
        let cache = ReachabilityEvaluationCache::new(
            scope,
            index
                .use_def_map(scope.file_scope_id(db))
                .reachability_constraints(),
        );
        match contents::snapshot_contents(db, scope, source, snapshot, ty, &cache) {
            contents::ContentsValue::Mapping(mapping) => {
                if mapping.builtin {
                    Ok(mapping.dictionary)
                } else {
                    Err(DictionaryFallback::Unavailable)
                }
            }
            contents::ContentsValue::Unreachable => Err(DictionaryFallback::Unreachable),
            contents::ContentsValue::Pending => Err(DictionaryFallback::Unavailable),
            contents::ContentsValue::Unavailable => Err(DictionaryFallback::Unavailable),
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
            dictionary.first_entry.set(db, env, Some(&name), ty);
            dictionary.items.insert(name, entry);
        }
        Ok(dictionary.finish())
    }

    /// Retain declared keys and their presence while preserving unknown hidden fields.
    pub(crate) fn from_typed_dict(unpacked: UnpackedTypedDict<'db>, source: TextRange) -> Self {
        let UnpackedTypedDict {
            keys,
            openness,
            has_implicit_extra_items,
        } = unpacked;
        Self {
            first_entry: DictionaryFirstEntry::Unknown,
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
            extra_items: if has_implicit_extra_items {
                DictionaryExtraItems::Value(Type::unknown())
            } else {
                openness
                    .effective_extra_items()
                    .map_or(DictionaryExtraItems::Closed, |extra| {
                        DictionaryExtraItems::Value(extra.declared_ty)
                    })
            },
        }
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
            // Hidden TypedDict fields follow a different call policy from ordinary mapping
            // values. Preserve the existing literal inference until that provenance is retained.
            if unpacked.has_implicit_extra_items {
                return None;
            }
            return Some(Self::from_typed_dict(unpacked, source));
        }
        let (key_ty, value_ty) = ty.unpack_keys_and_items(db, env)?;
        if key_ty.resolve_type_alias(db).is_never() || value_ty.resolve_type_alias(db).is_never() {
            return Some(Self {
                items: Box::default(),
                extra_items: DictionaryExtraItems::Closed,
                first_entry: DictionaryFirstEntry::Empty,
            });
        }
        let str_ty = KnownClass::Str.to_instance(db, env);
        if key_ty.is_assignable_to(db, env, str_ty) && !str_ty.is_assignable_to(db, env, key_ty) {
            // The ordinary mapping checker handles key domains that exclude some strings.
            // A homogeneous residual would incorrectly apply their values to other names.
            // Non-string keys retain the call checker's separate key-type diagnostic.
            return None;
        }
        Some(Self {
            items: Box::default(),
            extra_items: DictionaryExtraItems::Value(value_ty),
            first_entry: DictionaryFirstEntry::Unknown,
        })
    }
}

/// An ordered overlay of mapping sources. The residual excludes every represented name.
struct DictionaryItemsBuilder<'db> {
    items: FxIndexMap<Name, DictionaryItem<'db>>,
    extra_items: Option<Type<'db>>,
    first_entry: DictionaryFirstEntry<'db>,
}

impl Default for DictionaryItemsBuilder<'_> {
    fn default() -> Self {
        Self {
            items: FxIndexMap::default(),
            extra_items: None,
            first_entry: DictionaryFirstEntry::Empty,
        }
    }
}

impl<'db> DictionaryItemsBuilder<'db> {
    fn overlay(
        &mut self,
        db: &'db dyn Db,
        env: &ProgramEnvironment<'db>,
        dictionary: DictionaryItems<'db>,
    ) {
        match &mut self.first_entry {
            DictionaryFirstEntry::Empty => self.first_entry = dictionary.first_entry.clone(),
            DictionaryFirstEntry::Unknown => {}
            DictionaryFirstEntry::Entry { key, value } => {
                if let Some(key) = key {
                    if let Some(item) = dictionary.items.iter().find(|item| &item.name == key) {
                        *value = if item.is_required() {
                            item.ty
                        } else {
                            UnionType::from_two_elements(db, env, *value, item.ty)
                        };
                    } else if let DictionaryExtraItems::Value(ty) = dictionary.extra_items {
                        *value = UnionType::from_two_elements(db, env, *value, ty);
                    }
                } else {
                    for item in &dictionary.items {
                        *value = UnionType::from_two_elements(db, env, *value, item.ty);
                    }
                    if let DictionaryExtraItems::Value(ty) = dictionary.extra_items {
                        *value = UnionType::from_two_elements(db, env, *value, ty);
                    }
                }
            }
        }
        let DictionaryItems {
            items,
            extra_items,
            first_entry: _,
        } = dictionary;
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
        let Self {
            items,
            extra_items,
            first_entry,
        } = self;
        DictionaryItems {
            first_entry,
            items: items.into_values().collect(),
            extra_items: extra_items
                .map_or(DictionaryExtraItems::Closed, DictionaryExtraItems::Value),
        }
    }
}
