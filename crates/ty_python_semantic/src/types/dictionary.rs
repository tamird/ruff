use indexmap::map::Entry;
use ruff_python_ast::{self as ast, name::Name};
use ruff_text_size::{Ranged, TextRange};
use rustc_hash::FxHashSet;
use ty_python_core::scope::ScopeId;
use ty_python_core::semantic_index;

use crate::reachability::ReachabilityEvaluationCache;
use crate::types::call::collect_keyword_items;
use crate::types::infer::FunctionBodyDomain;
use crate::types::set_theoretic::UnionBuilder;
use crate::types::typed_dict::{
    UnpackedTypedDict, UnpackedTypedDictKey, extract_unpacked_typed_dict_from_value_type,
};
use crate::types::{
    BoundTypeVarInstance, IntersectionType, KnownClass, MemberLookupPolicy, ProgramEnvironment,
    Truthiness, Type, TypedDictOpenness, TypedDictType, UnionType,
};
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
    mut expression_type: impl FnMut(&ast::Expr) -> Option<Type<'db>>,
) -> Option<Type<'db>> {
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
    match mapping.dictionary.first_entry {
        DictionaryFirstEntry::Entry { key: _, value } => Some(value),
        DictionaryFirstEntry::Unknown => None,
        DictionaryFirstEntry::Empty => None,
    }
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

/// Observe one key through builtin dictionary history. Writable receiver types remain
/// unchanged; only the result of a successful read is refined by these contents facts.
pub(crate) fn item_type_at_use<'db>(
    db: &'db dyn Db,
    scope: ScopeId<'db>,
    subscript: &ast::ExprSubscript,
    receiver_type: Type<'db>,
    key_type: Type<'db>,
    reachability: &ReachabilityEvaluationCache<'db>,
) -> Option<Type<'db>> {
    let key = key_type.string_literal_value(db)?;
    let contents = contents::snapshot_contents(
        db,
        scope,
        &subscript.value,
        subscript.into(),
        receiver_type,
        reachability,
    );
    let mapping = match contents {
        contents::ContentsValue::Mapping(mapping) => mapping,
        contents::ContentsValue::Unreachable => return Some(Type::Never),
        contents::ContentsValue::Pending | contents::ContentsValue::Unavailable => return None,
    };
    if !mapping.builtin {
        return None;
    }
    mapping
        .dictionary
        .items
        .iter()
        .find(|item| item.name == key)
        .map(|item| item.ty)
}

pub(crate) fn key_membership_at_use<'db>(
    db: &'db dyn Db,
    scope: ScopeId<'db>,
    receiver: &ast::Expr,
    receiver_type: Type<'db>,
    key: &str,
    reachability: &ReachabilityEvaluationCache<'db>,
) -> Option<Truthiness> {
    let contents::ContentsValue::Mapping(mapping) = contents::snapshot_contents(
        db,
        scope,
        receiver,
        receiver.into(),
        receiver_type,
        reachability,
    ) else {
        return None;
    };
    if !mapping.builtin {
        return None;
    }
    Some(
        match mapping
            .dictionary
            .items
            .iter()
            .find(|item| item.name == key)
        {
            Some(item) => {
                if item.is_required() {
                    Truthiness::AlwaysTrue
                } else if item.ty.resolve_type_alias(db).is_never() {
                    Truthiness::AlwaysFalse
                } else {
                    Truthiness::Ambiguous
                }
            }
            None => {
                if mapping.dictionary.is_complete() {
                    Truthiness::AlwaysFalse
                } else {
                    Truthiness::Ambiguous
                }
            }
        },
    )
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
    /// The dictionary contains exactly the keyword arguments of this `ParamSpec` component.
    /// Named entries describe facts about those arguments. Operations that change the contents
    /// discard the component identity.
    ParamSpec(ParamSpecKeywords<'db>),
    /// An untouched captured keyword component plus disjoint named fields.
    KeywordTail(CapturedKeywordTail<'db>),
}

/// The keyword arguments captured by a `ParamSpec`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, get_size2::GetSize, salsa::SalsaValue)]
pub struct ParamSpecKeywords<'db>(BoundTypeVarInstance<'db>);

/// Proof that the named fields of a keyword dictionary are disjoint from its captured tail.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, get_size2::GetSize, salsa::SalsaValue)]
pub struct CapturedKeywordTail<'db> {
    component: ParamSpecKeywords<'db>,
    fixed: TypedDictType<'db>,
}

impl<'db> CapturedKeywordTail<'db> {
    /// Construct only from normalized overload parameters whose source ownership was proved by
    /// the argument binder. Named parameters of that overload are disjoint from its keyword tail.
    pub(super) fn from_overload(
        db: &'db dyn Db,
        component: BoundTypeVarInstance<'db>,
        fixed: TypedDictType<'db>,
    ) -> Option<Self> {
        (component.is_captured_keyword_arguments(db)
            && matches!(fixed.openness(db), TypedDictOpenness::Closed)
            && !fixed.items(db).is_empty())
        .then_some(Self {
            component: ParamSpecKeywords(component),
            fixed,
        })
    }
}

impl<'db> ParamSpecKeywords<'db> {
    fn from_type(db: &'db dyn Db, ty: Type<'db>) -> Option<Self> {
        let Type::TypeVar(component) = ty else {
            return None;
        };
        component
            .is_keyword_argument_component(db)
            .then_some(Self(component))
    }
}

impl<'db> DictionaryExtraItems<'db> {
    pub(super) fn keyword_paramspec(self, db: &'db dyn Db) -> Option<BoundTypeVarInstance<'db>> {
        match self {
            Self::ParamSpec(ParamSpecKeywords(component))
            | Self::KeywordTail(CapturedKeywordTail {
                component: ParamSpecKeywords(component),
                fixed: _,
            }) if component.is_captured_keyword_arguments(db) => Some(component.paramspec_base(db)),
            _ => None,
        }
    }

    /// The type of one additional mapping value.
    pub fn value_type(self) -> Option<Type<'db>> {
        match self {
            Self::Closed => None,
            Self::Value(ty) => Some(ty),
            Self::ParamSpec(_) | Self::KeywordTail(_) => Some(Type::object()),
        }
    }

    /// The type supplied while matching a keyword argument to a parameter. A `ParamSpec`
    /// component must retain its identity here, just as it does for a direct `**kwargs` argument.
    pub(super) fn argument_type(self) -> Option<Type<'db>> {
        match self {
            Self::ParamSpec(ParamSpecKeywords(component))
            | Self::KeywordTail(CapturedKeywordTail {
                component: ParamSpecKeywords(component),
                fixed: _,
            }) => Some(Type::TypeVar(component)),
            _ => self.value_type(),
        }
    }

    fn forget_paramspec(self) -> Self {
        match self {
            Self::ParamSpec(_) | Self::KeywordTail(_) => Self::Value(Type::object()),
            _ => self,
        }
    }

    pub(super) fn combine(
        self,
        db: &'db dyn Db,
        env: &ProgramEnvironment<'db>,
        incoming: Self,
        previous_empty: bool,
        incoming_empty: bool,
    ) -> Self {
        if previous_empty {
            return incoming;
        }
        if incoming_empty {
            return self;
        }
        match (self.value_type(), incoming.value_type()) {
            (None, None) => Self::Closed,
            (Some(ty), None) | (None, Some(ty)) => Self::Value(ty),
            (Some(left), Some(right)) => {
                Self::Value(UnionType::from_two_elements(db, env, left, right))
            }
        }
    }
}

/// A direct field read keyed by the same local name as the comprehension's output key.
fn comprehension_field_source<'db>(
    db: &'db dyn Db,
    key: &ast::Expr,
    value: &ast::Expr,
    expression_type: &mut impl FnMut(&ast::Expr) -> Option<Type<'db>>,
) -> Option<TypedDictType<'db>> {
    let output_key = key.as_name_expr()?;
    let (receiver, lookup_key) = match value {
        ast::Expr::Subscript(subscript) => (subscript.value.as_ref(), subscript.slice.as_ref()),
        ast::Expr::Call(call) if call.arguments.keywords.is_empty() => {
            let attribute = call.func.as_attribute_expr()?;
            let [lookup_key] = call.arguments.args.as_ref() else {
                return None;
            };
            if attribute.attr.as_str() != "pop" {
                return None;
            }
            (attribute.value.as_ref(), lookup_key)
        }
        _ => return None,
    };
    // Reading a local receiver cannot rebind the key between its two uses.
    if !receiver.is_name_expr() || lookup_key.as_name_expr()?.id != output_key.id {
        return None;
    }
    let Type::TypedDict(source) = expression_type(receiver)?.resolve_type_alias(db) else {
        return None;
    };
    Some(source)
}

/// String literal keys visited by an unfiltered comprehension over a direct list or tuple display.
fn definite_comprehension_keys<'ast>(
    comprehension: &'ast ast::ExprDictComp,
    output: &ast::Expr,
) -> Option<FxHashSet<&'ast str>> {
    let [generator] = comprehension.generators.as_ref() else {
        return None;
    };
    if generator.is_async
        || !generator.ifs.is_empty()
        || generator.target.as_name_expr()?.id != output.as_name_expr()?.id
    {
        return None;
    }
    let elements = match &generator.iter {
        ast::Expr::List(list) => &list.elts,
        ast::Expr::Tuple(tuple) => &tuple.elts,
        _ => return None,
    };
    elements
        .iter()
        .map(|element| {
            element
                .as_string_literal_expr()
                .map(|literal| literal.value.to_str())
        })
        .collect()
}

impl<'db> DictionaryItems<'db> {
    fn value_at(&self, name: &Name) -> Type<'db> {
        self.items
            .iter()
            .find(|item| &item.name == name)
            .map_or_else(|| self.extra_value(), |item| item.ty)
    }

    fn extra_value(&self) -> Type<'db> {
        self.extra_items.value_type().unwrap_or(Type::Never)
    }

    fn join(
        &self,
        db: &'db dyn Db,
        env: &ProgramEnvironment<'db>,
        other: &Self,
        uses_residual_presence: bool,
    ) -> Self {
        let extra_value =
            UnionType::from_two_elements(db, env, self.extra_value(), other.extra_value());
        let mut items: FxIndexMap<_, _> = self
            .items
            .iter()
            .map(|item| (item.name.clone(), item.clone()))
            .collect();
        for item in &other.items {
            items
                .entry(item.name.clone())
                .or_insert_with(|| item.clone());
        }
        for (name, item) in &mut items {
            let left = self.items.iter().find(|item| &item.name == name);
            let right = other.items.iter().find(|item| &item.name == name);
            item.ty =
                UnionType::from_two_elements(db, env, self.value_at(name), other.value_at(name));
            item.kind = if uses_residual_presence {
                DictionaryItemKind::Residual
            } else if left.is_some_and(DictionaryItem::is_required)
                && right.is_some_and(DictionaryItem::is_required)
            {
                DictionaryItemKind::Required
            } else if left
                .into_iter()
                .chain(right)
                .any(|item| item.kind != DictionaryItemKind::Residual)
            {
                DictionaryItemKind::Optional
            } else {
                DictionaryItemKind::Residual
            };
        }
        Self {
            first_entry: self.first_entry.join(db, env, &other.first_entry),
            items: items.into_values().collect(),
            extra_items: match (self.extra_items, other.extra_items) {
                (
                    left @ (DictionaryExtraItems::ParamSpec(_)
                    | DictionaryExtraItems::KeywordTail(_)),
                    right,
                ) if left == right => left,
                _ if extra_value.is_never() => DictionaryExtraItems::Closed,
                _ => DictionaryExtraItems::Value(extra_value),
            },
        }
    }

    /// Whether the named entries account for every possible key.
    pub const fn is_complete(&self) -> bool {
        matches!(self.extra_items, DictionaryExtraItems::Closed)
    }

    /// Observe the expression's contents only when its syntax does not determine its items.
    pub(crate) fn expression_or_observed(
        db: &'db dyn Db,
        env: &ProgramEnvironment<'db>,
        scope: ScopeId<'db>,
        expression: &ast::Expr,
        body_domain: Option<FunctionBodyDomain<'db>>,
        expression_type: &mut impl FnMut(&ast::Expr) -> Option<Type<'db>>,
        observe: impl FnOnce() -> DictionaryObservation<'db>,
    ) -> DictionaryObservation<'db> {
        match Self::expression(db, env, scope, expression, body_domain, expression_type) {
            Err(DictionaryFallback::Unavailable) => observe(),
            result => result,
        }
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

    pub(crate) fn unpacked_keyword(
        db: &'db dyn Db,
        scope: ScopeId<'db>,
        expression: &ast::Expr,
        call: &ast::ExprCall,
        name: &str,
        reachability: &ReachabilityEvaluationCache<'db>,
    ) -> Option<Self> {
        contents::unpacked_keyword(db, scope, expression, call, name, reachability)
    }

    /// Observe syntax whose result is a builtin dictionary.
    pub(crate) fn expression(
        db: &'db dyn Db,
        env: &ProgramEnvironment<'db>,
        scope: ScopeId<'db>,
        expression: &ast::Expr,
        domain: Option<FunctionBodyDomain<'db>>,
        expression_type: &mut impl FnMut(&ast::Expr) -> Option<Type<'db>>,
    ) -> DictionaryObservation<'db> {
        match expression {
            ast::Expr::If(conditional) => {
                let test_type = expression_type(&conditional.test);
                if test_type.is_some_and(|ty| ty.resolve_type_alias(db).is_never()) {
                    return Err(DictionaryFallback::Unreachable);
                }
                let truthiness = test_type
                    .and_then(|ty| ty.bool_if_inhabited(db, env))
                    .unwrap_or(Truthiness::Ambiguous);
                let mut observe = |branch: &ast::Expr| {
                    Self::builtin_source(
                        db,
                        env,
                        scope,
                        branch.into(),
                        branch,
                        domain,
                        expression_type,
                    )
                };
                match truthiness {
                    Truthiness::AlwaysTrue => return observe(&conditional.body),
                    Truthiness::AlwaysFalse => return observe(&conditional.orelse),
                    Truthiness::Ambiguous => {}
                }
                match (observe(&conditional.body), observe(&conditional.orelse)) {
                    (Ok(left), Ok(right)) => Ok(left.join(db, env, &right, false)),
                    (Err(DictionaryFallback::Unreachable), other)
                    | (other, Err(DictionaryFallback::Unreachable)) => other,
                    _ => Err(DictionaryFallback::Unavailable),
                }
            }
            ast::Expr::BinOp(binary) => {
                Self::union(db, env, scope, binary, domain, expression_type)
            }
            ast::Expr::Dict(_) => {
                Self::literal(db, env, scope, expression, domain, expression_type)
            }
            ast::Expr::DictComp(comprehension) => {
                let ast::ExprDictComp {
                    node_index: _,
                    range: _,
                    key,
                    value,
                    generators: _,
                } = comprehension;
                let key = key.as_deref().ok_or(DictionaryFallback::Unavailable)?;
                let definite_keys = definite_comprehension_keys(comprehension, key);
                if definite_keys.as_ref().is_some_and(FxHashSet::is_empty) {
                    return Ok(DictionaryItemsBuilder::default().finish());
                }
                let key_ty = expression_type(key).ok_or(DictionaryFallback::Unavailable)?;
                let value_ty = expression_type(value).ok_or(DictionaryFallback::Unavailable)?;
                let resolved_value = value_ty.resolve_type_alias(db);
                if resolved_value.is_never() || resolved_value.is_divergent() {
                    // A bottom body can be skipped by an empty iterator or a filter. It does not
                    // establish either an unreachable comprehension or a supplied keyword.
                    return Err(DictionaryFallback::Unavailable);
                }
                let key_ty = UnionBuilder::new(db, env).add(key_ty).build();
                let source = comprehension_field_source(db, key, value, expression_type);
                if let Some(source) = source
                    && key_ty == KnownClass::Str.to_instance(db, env)
                {
                    // A successful lookup preserves each source field's value type even when
                    // the iterator yields arbitrary strings. No particular key must be present.
                    let mut copied = Self::unpacked(db, env, Type::TypedDict(source), key.range())
                        .ok_or(DictionaryFallback::Unavailable)?;
                    for item in &mut copied.items {
                        item.ty = IntersectionType::from_two_elements(db, env, value_ty, item.ty);
                        item.kind = DictionaryItemKind::Residual;
                    }
                    return Ok(copied);
                }
                let keys = match &key_ty {
                    Type::Union(union) => union.elements(db),
                    ty => std::slice::from_ref(ty),
                };
                let source_fields = source.map(|source| source.items(db));
                let items = keys
                    .iter()
                    .map(|ty| {
                        let name = ty
                            .string_literal_value(db)
                            .ok_or(DictionaryFallback::Unavailable)?;
                        let ty = source_fields.and_then(|fields| fields.get(name)).map_or(
                            value_ty,
                            |field| {
                                IntersectionType::from_two_elements(
                                    db,
                                    env,
                                    value_ty,
                                    field.declared_type(),
                                )
                            },
                        );
                        Ok(DictionaryItem {
                            name: Name::new(name),
                            ty,
                            kind: if definite_keys
                                .as_ref()
                                .is_some_and(|keys| keys.contains(name))
                            {
                                DictionaryItemKind::Required
                            } else {
                                DictionaryItemKind::Residual
                            },
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
                let callee = expression_type(func).ok_or(DictionaryFallback::Unavailable)?;
                if let Type::FunctionLiteral(function) = callee
                    && arguments.is_empty()
                    && db.provided_module_precedes_call(scope, func, function.program_file(db))
                {
                    let mut items = function
                        .returned_dictionary_items(db)
                        .clone()
                        .ok_or(DictionaryFallback::Unavailable)?;
                    // Dictionary item spans belong to the observing file. The call is the
                    // origin available there; donor-file spans cannot be reused as offsets.
                    for item in &mut items.items {
                        item.source = expression.range();
                    }
                    return Ok(items);
                }
                let Type::ClassLiteral(class) = callee else {
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
                            domain,
                            expression_type,
                        )?;
                        dictionary.overlay(db, env, source);
                    }
                    _ => return Err(DictionaryFallback::Unavailable),
                }
                let keywords =
                    Self::keywords(db, env, scope, &arguments.keywords, domain, expression_type)?;
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
        domain: Option<FunctionBodyDomain<'db>>,
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
                    Self::unpacked_expression(db, env, scope, value, domain, expression_type)
                }
            }),
        )
    }

    fn unpacked_expression(
        db: &'db dyn Db,
        env: &ProgramEnvironment<'db>,
        scope: ScopeId<'db>,
        expression: &ast::Expr,
        domain: Option<FunctionBodyDomain<'db>>,
        expression_type: &mut impl FnMut(&ast::Expr) -> Option<Type<'db>>,
    ) -> DictionaryObservation<'db> {
        let observed = Self::expression(db, env, scope, expression, domain, expression_type);
        if expression.is_dict_expr() || !matches!(observed, Err(DictionaryFallback::Unavailable)) {
            // Unsupported literals decline atomically; unreachable operands stay unreachable.
            return observed;
        }
        Self::unpacked_value(db, env, scope, expression, domain, expression_type)
    }

    fn unpacked_value(
        db: &'db dyn Db,
        env: &ProgramEnvironment<'db>,
        scope: ScopeId<'db>,
        expression: &ast::Expr,
        domain: Option<FunctionBodyDomain<'db>>,
        expression_type: &mut impl FnMut(&ast::Expr) -> Option<Type<'db>>,
    ) -> DictionaryObservation<'db> {
        let ty = expression_type(expression).ok_or(DictionaryFallback::Unavailable)?;
        let index = semantic_index(db, scope.program_file(db));
        let cache = ReachabilityEvaluationCache::new(
            scope,
            index
                .use_def_map(scope.file_scope_id(db))
                .reachability_constraints(),
        )
        .with_body_domain(domain.filter(|domain| domain.scope(db) == scope));
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
        domain: Option<FunctionBodyDomain<'db>>,
        expression_type: &mut impl FnMut(&ast::Expr) -> Option<Type<'db>>,
    ) -> DictionaryObservation<'db> {
        if ty_python_core::place::PlaceExpr::try_from_expr(source).is_none() {
            return Self::unpacked_expression(db, env, scope, source, domain, expression_type);
        }
        let ty = expression_type(source).ok_or(DictionaryFallback::Unavailable)?;
        let index = semantic_index(db, scope.program_file(db));
        let cache = ReachabilityEvaluationCache::new(
            scope,
            index
                .use_def_map(scope.file_scope_id(db))
                .reachability_constraints(),
        )
        .with_body_domain(domain.filter(|domain| domain.scope(db) == scope));
        match contents::at_snapshot(db, scope, source, snapshot, ty, &cache) {
            Err(DictionaryFallback::Unavailable) => {
                Self::unpacked(db, env, ty, source.range()).ok_or(DictionaryFallback::Unavailable)
            }
            observed => observed,
        }
    }

    pub(super) fn union(
        db: &'db dyn Db,
        env: &ProgramEnvironment<'db>,
        scope: ScopeId<'db>,
        binary: &ast::ExprBinOp,
        domain: Option<FunctionBodyDomain<'db>>,
        expression_type: &mut impl FnMut(&ast::Expr) -> Option<Type<'db>>,
    ) -> DictionaryObservation<'db> {
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
                binary.into(),
                operand,
                domain,
                expression_type,
            )
            .or_else(|fallback| match fallback {
                DictionaryFallback::Unavailable => {
                    let ty = expression_type(operand).ok_or(fallback)?;
                    let unpacked =
                        extract_unpacked_typed_dict_from_value_type(db, env, ty).ok_or(fallback)?;
                    let has_implicit_extra_items = unpacked.has_implicit_extra_items;
                    let mut source = Self::from_typed_dict(unpacked, operand.range());
                    if has_implicit_extra_items {
                        // A hidden RHS field can overwrite any known LHS field.
                        source.extra_items = DictionaryExtraItems::Value(Type::object());
                    }
                    Ok(source)
                }
                DictionaryFallback::Unreachable => Err(fallback),
            })?;
            dictionary.overlay(db, env, source);
        }
        Ok(dictionary.finish())
    }

    /// Union dispatch requires a builtin allocation, not just a nominal dictionary type.
    pub(super) fn builtin_source(
        db: &'db dyn Db,
        env: &ProgramEnvironment<'db>,
        scope: ScopeId<'db>,
        snapshot: ast::ExprRef<'_>,
        source: &ast::Expr,
        domain: Option<FunctionBodyDomain<'db>>,
        expression_type: &mut impl FnMut(&ast::Expr) -> Option<Type<'db>>,
    ) -> DictionaryObservation<'db> {
        if ty_python_core::place::PlaceExpr::try_from_expr(source).is_none() {
            return Self::expression(db, env, scope, source, domain, expression_type);
        }
        let ty = expression_type(source).ok_or(DictionaryFallback::Unavailable)?;
        let index = semantic_index(db, scope.program_file(db));
        let cache = ReachabilityEvaluationCache::new(
            scope,
            index
                .use_def_map(scope.file_scope_id(db))
                .reachability_constraints(),
        )
        .with_body_domain(domain.filter(|domain| domain.scope(db) == scope));
        contents::snapshot_contents(db, scope, source, snapshot, ty, &cache).builtin_items()
    }

    pub(super) fn literal(
        db: &'db dyn Db,
        env: &ProgramEnvironment<'db>,
        scope: ScopeId<'db>,
        expression: &ast::Expr,
        domain: Option<FunctionBodyDomain<'db>>,
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
                let unpacked =
                    Self::unpacked_expression(db, env, scope, value, domain, expression_type)?;
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
            dictionary.extra_items = dictionary.extra_items.forget_paramspec();
            dictionary.items.insert(name, entry);
        }
        Ok(dictionary.finish())
    }

    /// Recover declared `TypedDict` entries when expression observations are unavailable.
    pub(crate) fn from_typed_dict_type(
        db: &'db dyn Db,
        env: &ProgramEnvironment<'db>,
        ty: Type<'db>,
        source: TextRange,
    ) -> Option<Self> {
        let unpacked = extract_unpacked_typed_dict_from_value_type(db, env, ty)?;
        Some(Self::from_typed_dict(unpacked, source))
    }

    /// Retain declared keys and their presence while preserving unknown hidden fields.
    fn from_typed_dict(unpacked: UnpackedTypedDict<'db>, source: TextRange) -> Self {
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
    extra_items: DictionaryExtraItems<'db>,
    first_entry: DictionaryFirstEntry<'db>,
}

impl Default for DictionaryItemsBuilder<'_> {
    fn default() -> Self {
        Self {
            items: FxIndexMap::default(),
            extra_items: DictionaryExtraItems::Closed,
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
        let previous_empty =
            self.items.is_empty() && matches!(self.extra_items, DictionaryExtraItems::Closed);
        let incoming_empty = dictionary.items.is_empty() && dictionary.is_complete();
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
                    } else if let Some(ty) = dictionary.extra_items.value_type() {
                        *value = UnionType::from_two_elements(db, env, *value, ty);
                    }
                } else {
                    for item in &dictionary.items {
                        *value = UnionType::from_two_elements(db, env, *value, item.ty);
                    }
                    if let Some(ty) = dictionary.extra_items.value_type() {
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
        let incoming_extra = extra_items.value_type();
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
                        && let Some(ty) = self.extra_items.value_type()
                    {
                        item.ty = UnionType::from_two_elements(db, env, ty, item.ty);
                    }
                    entry.insert(item);
                }
            }
        }
        self.extra_items =
            self.extra_items
                .combine(db, env, extra_items, previous_empty, incoming_empty);
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
            extra_items,
        }
    }
}
