use crate::types::dictionary::{
    DictionaryExtraItems, DictionaryFallback, DictionaryItem, DictionaryItemKind, DictionaryItems,
    DictionaryObservation,
};
use crate::{Db, FxIndexMap};
use std::borrow::Cow;
use std::cell::OnceCell;
use std::fmt::Display;

use indexmap::map::Entry;
use itertools::{Either, Itertools};
use ruff_python_ast as ast;
use ruff_python_ast::name::Name;
use rustc_hash::{FxHashMap, FxHashSet};

use crate::ProgramEnvironment;
use crate::types::signatures::Parameters;
use crate::types::typed_dict::extract_unpacked_typed_dict_keys_from_value_type;
use crate::types::{Type, TypeContext, UnionType, expand_type};

/// Maximum total number of expanded argument type combinations across all arguments
/// in [`CallArgumentExpansions::iter`].
///
/// See: [pyright's `maxTotalOverloadArgTypeExpansionCount`][pyright]
///
/// [pyright]: https://github.com/microsoft/pyright/blob/5a325e4874e775436671eed65ad696787a1ef74b/packages/pyright-internal/src/analyzer/typeEvaluator.ts#L566
const MAX_TOTAL_EXPANSION: usize = 256;

/// Combine keyword sources on paths where their call succeeds. Unlike dictionary overlays,
/// separate keyword sources cannot overwrite a supplied name: a collision raises instead.
pub(crate) fn collect_keyword_items<'db>(
    db: &'db dyn Db,
    env: &ProgramEnvironment<'db>,
    sources: impl IntoIterator<Item = DictionaryObservation<'db>>,
) -> DictionaryObservation<'db> {
    let mut items: FxIndexMap<Name, DictionaryItem<'db>> = FxIndexMap::default();
    let mut extra_items = None;
    for source in sources {
        let DictionaryItems {
            items: incoming,
            extra_items: incoming_extra,
        } = source?;
        let incoming_extra = match incoming_extra {
            DictionaryExtraItems::Closed => None,
            DictionaryExtraItems::Value(ty) => Some(ty),
        };
        if let Some(ty) = incoming_extra {
            let names: FxHashSet<_> = incoming.iter().map(|item| item.name.clone()).collect();
            for item in items.values_mut() {
                if !item.is_required() && !names.contains(&item.name) {
                    item.ty = UnionType::from_two_elements(db, env, item.ty, ty);
                }
            }
        }
        for mut item in incoming {
            match items.entry(item.name.clone()) {
                Entry::Occupied(mut entry) => {
                    let previous = entry.get();
                    if previous.kind != DictionaryItemKind::Residual
                        && item.kind != DictionaryItemKind::Residual
                    {
                        // Decline metadata for possibly colliding named arguments. The ordinary
                        // call checker retains responsibility for their diagnostics.
                        return Err(DictionaryFallback::Unavailable);
                    }
                    if previous.is_required() {
                        continue;
                    }
                    if !item.is_required() {
                        item.ty = UnionType::from_two_elements(db, env, previous.ty, item.ty);
                        if item.kind == DictionaryItemKind::Residual {
                            item.kind = previous.kind;
                            item.source = previous.source;
                        }
                    }
                    entry.insert(item);
                }
                Entry::Vacant(entry) => {
                    if !item.is_required()
                        && let Some(ty) = extra_items
                    {
                        item.ty = UnionType::from_two_elements(db, env, ty, item.ty);
                    }
                    entry.insert(item);
                }
            }
        }
        if let Some(ty) = incoming_extra {
            extra_items = Some(extra_items.map_or(ty, |previous| {
                UnionType::from_two_elements(db, env, previous, ty)
            }));
        }
    }
    Ok(DictionaryItems {
        items: items.into_values().collect(),
        extra_items: extra_items.map_or(DictionaryExtraItems::Closed, DictionaryExtraItems::Value),
    })
}

#[derive(Clone, Copy, Debug)]
pub(crate) enum Argument<'a> {
    /// The synthetic `self` or `cls` argument, which doesn't appear explicitly at the call site.
    Synthetic,
    /// A positional argument.
    Positional,
    /// A starred positional argument (e.g. `*args`) containing the specified number of elements.
    Variadic,
    /// A keyword argument (e.g. `a=1`).
    Keyword(&'a str),
    /// The double-starred keywords argument (e.g. `**kwargs`).
    Keywords,
}

/// Arguments for a single call, in source order, along with inferred types for each argument.
#[derive(Clone, Debug, Default)]
pub(crate) struct CallArguments<'a, 'db> {
    request_input_proof: bool,
    items: Vec<CallArgument<'a, 'db>>,
}

#[derive(Clone, Debug)]
struct CallArgument<'a, 'db> {
    argument: Argument<'a>,
    types: CallArgumentTypes<'db>,
    known_unpacking: Option<KnownUnpacking<'db>>,
}

/// Arguments whose expanded alternatives have all satisfied their declared parameters.
///
/// Argument inference can replay after overload checking. Retain the complete inputs so a
/// successful expansion cannot certify different committed arguments.
#[derive(Clone, Debug)]
pub(super) struct CallArgumentsSnapshot<'db> {
    items: Box<[SavedCallArgument<'db>]>,
}

impl<'db> CallArgumentsSnapshot<'db> {
    pub(super) fn matches(&self, arguments: &CallArguments<'_, 'db>) -> bool {
        let Self { items } = self;
        let CallArguments {
            request_input_proof: _,
            items: current_items,
        } = arguments;
        items.len() == current_items.len()
            && items.iter().zip(current_items).all(|(saved, current)| {
                let SavedCallArgument {
                    argument,
                    types,
                    known_unpacking,
                } = saved;
                let CallArgument {
                    argument: current_argument,
                    types: current_types,
                    known_unpacking: current_unpacking,
                } = current;
                argument.matches(*current_argument)
                    && types.has_same_lookups(current_types)
                    && known_unpacking == current_unpacking
            })
    }
}

#[derive(Clone, Debug)]
struct SavedCallArgument<'db> {
    argument: OwnedArgument,
    types: CallArgumentTypes<'db>,
    known_unpacking: Option<KnownUnpacking<'db>>,
}

#[derive(Clone, Debug)]
enum OwnedArgument {
    Synthetic,
    Positional,
    Variadic,
    Keyword(Name),
    Keywords,
}

impl OwnedArgument {
    fn matches(&self, argument: Argument<'_>) -> bool {
        match argument {
            Argument::Synthetic => matches!(self, Self::Synthetic),
            Argument::Positional => matches!(self, Self::Positional),
            Argument::Variadic => matches!(self, Self::Variadic),
            Argument::Keyword(name) => match self {
                Self::Keyword(saved) => saved == name,
                _ => false,
            },
            Argument::Keywords => matches!(self, Self::Keywords),
        }
    }
}

/// Known elements of an unpacked argument.
///
/// These values supplement the container type: `list[int | str]` alone cannot retain the
/// argument count or associate each element with its parameter. Keyword inventories may include
/// a residual value type for additional names; individual known keys can be optional.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) enum KnownUnpacking<'db> {
    Positional(Box<[Type<'db>]>),
    Keywords(KnownKeywords<'db>),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct KnownKeywords<'db> {
    pub(super) items: Box<[DictionaryItem<'db>]>,
    pub(super) extra_items: Option<Type<'db>>,
    /// Prefix parameters removed while forwarding to a `ParamSpec` remain excluded from the tail.
    pub(super) excluded_names: Vec<Name>,
}

impl<'db> KnownKeywords<'db> {
    /// All values supplied without named-key evidence, after any `ParamSpec` projection.
    pub(super) fn residual_values(
        &self,
        db: &'db dyn Db,
        env: &ProgramEnvironment<'db>,
    ) -> Type<'db> {
        let Self {
            items,
            extra_items,
            excluded_names: _,
        } = self;
        UnionType::from_elements(
            db,
            env,
            extra_items.iter().copied().chain(
                items.iter().filter_map(|item| {
                    (item.kind == DictionaryItemKind::Residual).then_some(item.ty)
                }),
            ),
        )
    }

    pub(super) fn residual_value(
        &self,
        db: &'db dyn Db,
        name: Option<&str>,
        all_values: Type<'db>,
    ) -> Option<Type<'db>> {
        let Self {
            items,
            extra_items,
            excluded_names,
        } = self;
        let ty = if let Some(name) = name {
            if excluded_names.iter().any(|excluded| excluded == name) {
                return None;
            }
            if let Some(item) = items.iter().find(|item| item.name == name) {
                match item.kind {
                    DictionaryItemKind::Required => return None,
                    DictionaryItemKind::Optional => return None,
                    DictionaryItemKind::Residual => item.ty,
                }
            } else {
                (*extra_items)?
            }
        } else {
            all_values
        };
        (!ty.resolve_type_alias(db).is_never()).then_some(ty)
    }
}

impl<'db> KnownUnpacking<'db> {
    fn positional(
        expression: &ast::Expr,
        expression_type: &mut impl FnMut(&ast::Expr) -> Option<Type<'db>>,
    ) -> Option<Self> {
        let elements = match expression {
            ast::Expr::List(ast::ExprList {
                node_index: _,
                range: _,
                elts,
                ctx: _,
            }) => elts,
            ast::Expr::Tuple(ast::ExprTuple {
                node_index: _,
                range: _,
                elts,
                ctx: _,
                parenthesized: _,
            }) => elts,
            _ => return None,
        };
        let types = elements
            .iter()
            .map(|element| {
                if element.is_starred_expr() {
                    None
                } else {
                    expression_type(element)
                }
            })
            .collect::<Option<Box<[_]>>>()?;
        Some(Self::Positional(types))
    }

    fn keywords(dictionary: DictionaryItems<'db>) -> Self {
        let DictionaryItems { items, extra_items } = dictionary;
        let extra_items = match extra_items {
            DictionaryExtraItems::Closed => None,
            DictionaryExtraItems::Value(ty) => Some(ty),
        };
        Self::Keywords(KnownKeywords {
            items,
            extra_items,
            excluded_names: Vec::new(),
        })
    }
}

/// Inferred types for a given argument.
///
/// Note that a single argument may produce multiple distinct inferred types when inferred
/// with type context across multiple bindings.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct CallArgumentTypes<'db> {
    fallback_type: Option<Type<'db>>,
    types: FxHashMap<Type<'db>, Type<'db>>,
}

impl<'db> CallArgumentTypes<'db> {
    /// Compare the types observed by binding, independently of redundant context entries.
    fn has_same_lookups(&self, other: &Self) -> bool {
        self.get_default() == other.get_default()
            && self.types.keys().chain(other.types.keys()).all(|context| {
                self.try_get_for_declared_type(*context)
                    == other.try_get_for_declared_type(*context)
            })
    }

    fn new(fallback_ty: Option<Type<'db>>) -> Self {
        Self {
            fallback_type: fallback_ty,
            types: FxHashMap::default(),
        }
    }

    /// Returns the most appropriate type of this argument when there is no specific declared type.
    pub(crate) fn get_default(&self) -> Option<Type<'db>> {
        // If this type was inferred against exactly one declared type, or was inferred against
        // multiple, but resulted in a single inferred type, we have an exact type to return.
        if let Ok(exact_ty) = self
            .types
            .values()
            .exactly_one()
            .or_else(|_| self.types.values().all_equal_value())
        {
            return Some(*exact_ty);
        }

        self.fallback_type
    }

    /// Returns the type of this argument when inferred against the provided declared type.
    ///
    /// If the type was not inferred against the declared type directly, this method will fall back to
    /// [`Self::get_default`].
    pub(crate) fn try_get_for_declared_type(&self, tcx: Type<'db>) -> Option<Type<'db>> {
        self.types.get(&tcx).copied().or_else(|| self.get_default())
    }

    /// Returns the type of this argument when inferred against the provided declared type.
    ///
    /// If the type was not inferred against the declared type directly, this method will fall back to
    /// [`Self::get_default`], or to `Unknown` if no fallback type exists.
    pub(crate) fn get_for_declared_type(&self, tcx: Type<'db>) -> Type<'db> {
        self.try_get_for_declared_type(tcx)
            .unwrap_or(Type::unknown())
    }

    /// Insert the type of this argument when inferred with the provided type context.
    fn insert(&mut self, tcx: impl Into<TypeContext<'db>>, ty: Type<'db>) {
        match tcx.into().annotation {
            None => self.fallback_type = Some(ty),
            Some(tcx) => {
                self.types.insert(tcx, ty);
            }
        }
    }

    fn iter(&self) -> impl Iterator<Item = (TypeContext<'db>, Type<'db>)> {
        self.types
            .iter()
            .map(|(tcx, ty)| (TypeContext::new(Some(*tcx)), *ty))
            .chain(self.fallback_type.map(|ty| (TypeContext::default(), ty)))
    }

    pub(crate) fn has_unspecialized_nominal_type(
        &self,
        db: &'db dyn Db,
        env: &ProgramEnvironment<'db>,
    ) -> bool {
        self.iter().any(|(_, ty)| {
            matches!(ty.resolve_type_alias(db), Type::NominalInstance(_))
                && ty.has_unspecialized_type_var(db, env)
        })
    }
}

impl<'a, 'db> CallArguments<'a, 'db> {
    pub(super) fn snapshot(&self) -> CallArgumentsSnapshot<'db> {
        let Self {
            request_input_proof: _,
            items,
        } = self;
        CallArgumentsSnapshot {
            items: items
                .iter()
                .map(|item| {
                    let CallArgument {
                        argument,
                        types,
                        known_unpacking,
                    } = item;
                    let argument = match argument {
                        Argument::Synthetic => OwnedArgument::Synthetic,
                        Argument::Positional => OwnedArgument::Positional,
                        Argument::Variadic => OwnedArgument::Variadic,
                        Argument::Keyword(name) => OwnedArgument::Keyword(Name::new(name)),
                        Argument::Keywords => OwnedArgument::Keywords,
                    };
                    SavedCallArgument {
                        argument,
                        types: types.clone(),
                        known_unpacking: known_unpacking.clone(),
                    }
                })
                .collect(),
        }
    }

    /// Create `CallArguments` from AST arguments. We will use the provided callback to obtain the
    /// type of each splatted argument, so that we can determine its length. All other arguments
    /// will remain uninitialized.
    pub(crate) fn from_arguments(
        arguments: &'a ast::Arguments,
        mut infer_argument_type: impl FnMut(&ast::ArgOrKeyword, &ast::Expr) -> Type<'db>,
    ) -> Self {
        let mut call_arguments = Self {
            items: Vec::with_capacity(arguments.len()),
            request_input_proof: false,
        };

        for arg_or_keyword in arguments.iter_source_order() {
            let (argument, ty) = match arg_or_keyword {
                ast::ArgOrKeyword::Arg(arg) => match arg {
                    ast::Expr::Starred(ast::ExprStarred { value, .. }) => {
                        let ty = infer_argument_type(&arg_or_keyword, value);
                        (Argument::Variadic, Some(ty))
                    }
                    _ => (Argument::Positional, None),
                },
                ast::ArgOrKeyword::Keyword(ast::Keyword { arg, value, .. }) => {
                    if let Some(arg) = arg {
                        (Argument::Keyword(&arg.id), None)
                    } else {
                        let ty = infer_argument_type(&arg_or_keyword, value);
                        (Argument::Keywords, Some(ty))
                    }
                }
            };
            call_arguments.items.push(CallArgument {
                argument,
                types: CallArgumentTypes::new(ty),
                known_unpacking: None,
            });
        }

        call_arguments
    }

    /// Like [`Self::from_arguments`] but fills as much typing info in as possible.
    ///
    /// This currently only exists for the LSP usecase, and shouldn't be used in normal
    /// typechecking.
    pub(crate) fn from_arguments_typed(
        arguments: &'a ast::Arguments,
        mut infer_argument_type: impl FnMut(&ast::Expr) -> Type<'db>,
    ) -> Self {
        arguments
            .iter_source_order()
            .map(|arg_or_keyword| match arg_or_keyword {
                ast::ArgOrKeyword::Arg(arg) => match arg {
                    ast::Expr::Starred(ast::ExprStarred { value, .. }) => {
                        let ty = infer_argument_type(value);
                        (Argument::Variadic, Some(ty))
                    }
                    _ => {
                        let ty = infer_argument_type(arg);
                        (Argument::Positional, Some(ty))
                    }
                },
                ast::ArgOrKeyword::Keyword(ast::Keyword { arg, value, .. }) => {
                    let ty = infer_argument_type(value);
                    if let Some(arg) = arg {
                        (Argument::Keyword(&arg.id), Some(ty))
                    } else {
                        (Argument::Keywords, Some(ty))
                    }
                }
            })
            .collect()
    }

    /// Retain exact contents after the argument expressions have been inferred.
    ///
    /// The callbacks read existing types and dictionary observations; they must not infer
    /// argument expressions again.
    #[must_use]
    pub(crate) fn with_known_unpacking(
        mut self,
        arguments: &ast::Arguments,
        mut expression_type: impl FnMut(&ast::Expr) -> Option<Type<'db>>,
        mut dictionary_items: impl FnMut(&ast::Expr) -> DictionaryObservation<'db>,
    ) -> Self {
        let Self {
            items,
            request_input_proof: _,
        } = &mut self;
        for (item, argument) in items.iter_mut().zip(arguments.iter_source_order()) {
            if item.types.get_default().is_some_and(|ty| ty.is_never()) {
                item.known_unpacking = None;
                continue;
            }
            item.known_unpacking = match argument {
                ast::ArgOrKeyword::Arg(expression) => match expression {
                    ast::Expr::Starred(ast::ExprStarred {
                        node_index: _,
                        range: _,
                        value,
                        ctx: _,
                    }) => KnownUnpacking::positional(value, &mut expression_type),
                    _ => None,
                },
                ast::ArgOrKeyword::Keyword(ast::Keyword {
                    range: _,
                    node_index: _,
                    arg,
                    value,
                }) => match arg {
                    Some(_) => None,
                    None => match dictionary_items(value) {
                        Err(DictionaryFallback::Unavailable) => None,
                        Err(DictionaryFallback::Unreachable) => {
                            item.types = CallArgumentTypes::new(Some(Type::Never));
                            None
                        }
                        Ok(dictionary) => Some(KnownUnpacking::keywords(dictionary)),
                    },
                },
            };
        }
        self
    }

    pub(super) fn known_unpacking(&self, index: usize) -> Option<&KnownUnpacking<'db>> {
        let Self {
            items,
            request_input_proof: _,
        } = self;
        let CallArgument {
            argument: _,
            types: _,
            known_unpacking,
        } = items.get(index)?;
        known_unpacking.as_ref()
    }

    /// Create a [`CallArguments`] with no arguments.
    pub(crate) fn none() -> Self {
        Self::default()
    }

    /// Create a [`CallArguments`] from an iterator over non-variadic positional argument types.
    pub(crate) fn positional(positional_tys: impl IntoIterator<Item = Type<'db>>) -> Self {
        positional_tys
            .into_iter()
            .map(|ty| (Argument::Positional, Some(ty)))
            .collect()
    }

    /// Request input requirements for implicit calls made while evaluating this call.
    pub(crate) fn with_input_proof_request(mut self, requested: bool) -> Self {
        self.request_input_proof = requested;
        self
    }

    pub(crate) fn set_input_proof_request(&mut self, requested: bool) {
        self.request_input_proof = requested;
    }

    pub(crate) fn requests_input_proof(&self) -> bool {
        self.request_input_proof
    }

    pub(crate) fn len(&self) -> usize {
        self.items.len()
    }

    pub(crate) fn is_variadic(&self, index: usize) -> bool {
        self.items.get(index).is_some_and(|argument| {
            matches!(argument.argument, Argument::Variadic | Argument::Keywords)
        })
    }

    pub(crate) fn argument_types(&self, index: usize) -> Option<&CallArgumentTypes<'db>> {
        self.items.get(index).map(|item| &item.types)
    }

    pub(crate) fn insert_type(
        &mut self,
        index: usize,
        tcx: impl Into<TypeContext<'db>>,
        ty: Type<'db>,
    ) {
        self.items
            .get_mut(index)
            .expect("argument index should be valid")
            .types
            .insert(tcx, ty);
    }

    pub(crate) fn clear_types(&mut self, index: usize) {
        self.items
            .get_mut(index)
            .expect("argument index should be valid")
            .types = CallArgumentTypes::default();
    }

    pub(crate) fn iter_types(&self) -> impl Iterator<Item = &CallArgumentTypes<'db>> + '_ {
        self.items.iter().map(|item| &item.types)
    }

    /// Returns `true` if the inferred types are equal for the given set of argument indices.
    pub(crate) fn inferred_types_equal_at(&self, other: &Self, argument_indices: &[usize]) -> bool {
        argument_indices.iter().all(|&index| {
            self.items.get(index).map(|item| &item.types)
                == other.items.get(index).map(|item| &item.types)
        })
    }

    /// Prepend an optional extra synthetic argument (for a `self` or `cls` parameter) to the front
    /// of this argument list. (If `bound_self` is none, we return the argument list
    /// unmodified.)
    pub(crate) fn with_self(&self, bound_self: Option<Type<'db>>) -> Cow<'_, Self> {
        if bound_self.is_some() {
            let mut items = Vec::with_capacity(self.items.len() + 1);
            items.push(CallArgument {
                argument: Argument::Synthetic,
                types: CallArgumentTypes::new(bound_self),
                known_unpacking: None,
            });
            items.extend(self.items.iter().cloned());
            Cow::Owned(CallArguments {
                items,
                request_input_proof: self.request_input_proof,
            })
        } else {
            Cow::Borrowed(self)
        }
    }

    pub(crate) fn iter(
        &self,
    ) -> impl Iterator<Item = (Argument<'a>, &CallArgumentTypes<'db>)> + '_ {
        self.items.iter().map(|item| (item.argument, &item.types))
    }

    /// Create a new [`CallArguments`] starting from the specified index.
    fn start_from(&self, index: usize) -> Self {
        Self {
            items: self.items[index..].to_vec(),
            request_input_proof: self.request_input_proof,
        }
    }

    /// Select arguments forwarded to a `ParamSpec`, excluding the wrapper's prefix keywords.
    ///
    /// The resulting argument list preserves the order of `indices`. Unlike [`Self::start_from`],
    /// this can project a non-contiguous subset of the original call arguments. This is used to
    /// turn the forwarded outer arguments into the argument list for a synthetic sub-call:
    ///
    /// ```py
    /// def wrapper[**P, R](func: Callable[P, R], **kwargs: P.kwargs) -> R: ...
    /// wrapper(TagSet=[...], func=f)  # select `TagSet=[...]`, but not the later `func=f`
    /// ```
    ///
    /// A keyword inventory can supply both prefix and forwarded parameters. Retain only the
    /// forwarded entries, preserving each entry's type, presence, and source location. A residual
    /// must not supply prefix keywords again in the forwarded call.
    pub(crate) fn select_for_paramspec(
        &self,
        indices: &[usize],
        parameters: &Parameters<'db>,
        prefix_len: usize,
    ) -> Self {
        Self {
            request_input_proof: self.request_input_proof,
            items: indices
                .iter()
                .map(|index| {
                    let CallArgument {
                        argument,
                        types,
                        known_unpacking,
                    } = &self.items[*index];
                    let known_unpacking =
                        known_unpacking.as_ref().map(|unpacking| match unpacking {
                            KnownUnpacking::Positional(_) => unpacking.clone(),
                            KnownUnpacking::Keywords(keywords) => {
                                let KnownKeywords {
                                    items,
                                    extra_items,
                                    excluded_names,
                                } = keywords;
                                let items = items
                                    .iter()
                                    .filter(|item| {
                                        parameters
                                            .keyword_by_name(&item.name)
                                            .is_none_or(|(index, _)| index >= prefix_len)
                                    })
                                    .cloned()
                                    .collect();
                                let mut excluded_names = excluded_names.clone();
                                excluded_names.extend(
                                    parameters
                                        .iter()
                                        .take(prefix_len)
                                        .filter_map(|parameter| parameter.keyword_name().cloned()),
                                );
                                KnownUnpacking::Keywords(KnownKeywords {
                                    items,
                                    extra_items: *extra_items,
                                    excluded_names,
                                })
                            }
                        });
                    CallArgument {
                        argument: *argument,
                        types: types.clone(),
                        known_unpacking,
                    }
                })
                .collect(),
        }
    }

    /// Returns the `functools.partial(...)` bound-argument slice and whether it is concrete enough
    /// to synthesize a precise partial signature.
    pub(crate) fn functools_partial_bound_arguments(
        &self,
        db: &'db dyn Db,
        env: &ProgramEnvironment<'db>,
    ) -> Option<(Self, bool)> {
        let bound_call_arguments = self.start_from(1);
        let mut can_synthesize_signature = true;

        for (argument, argument_ty) in bound_call_arguments.iter() {
            let argument_ty = argument_ty.get_default().unwrap_or_else(Type::unknown);
            match argument {
                Argument::Variadic => {
                    if !matches!(
                        argument_ty.tuple_instance_spec(db, env),
                        Some(spec) if spec.as_fixed_length().is_some()
                    ) {
                        return None;
                    }
                }
                Argument::Keywords => {
                    // Known `TypedDict` items can still be checked against their target
                    // parameters, even though possible hidden items prevent us from synthesizing
                    // a precise partial signature.
                    extract_unpacked_typed_dict_keys_from_value_type(db, env, argument_ty)?;
                    can_synthesize_signature = false;
                }
                Argument::Positional | Argument::Synthetic | Argument::Keyword(_) => {}
            }
        }

        Some((bound_call_arguments, can_synthesize_signature))
    }

    /// Prepares lazy argument type expansions for overload resolution.
    pub(super) fn expansions<'s>(
        &'s self,
        db: &'db dyn Db,
        env: &'s ProgramEnvironment<'db>,
    ) -> CallArgumentExpansions<'s, 'a, 'db> {
        CallArgumentExpansions {
            arguments: self,
            db,
            env,
            types: OnceCell::new(),
        }
    }

    pub(super) fn display<'env>(
        &'env self,
        db: &'db dyn Db,
        env: &'env ProgramEnvironment<'db>,
    ) -> impl Display + 'env {
        struct DisplayCallArgumentTypes<'env, 'a, 'db> {
            types: &'a CallArgumentTypes<'db>,
            db: &'db dyn Db,
            env: &'env ProgramEnvironment<'db>,
        }

        impl std::fmt::Display for DisplayCallArgumentTypes<'_, '_, '_> {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                let db = self.db;
                f.debug_map()
                    .entries(self.types.iter().map(|(tcx, ty)| {
                        (
                            tcx.annotation.as_ref().map(|ty| ty.display(db, self.env)),
                            ty.display(db, self.env),
                        )
                    }))
                    .finish()
            }
        }

        std::fmt::from_fn(move |f| {
            f.write_str("(")?;
            for (index, (argument, types)) in self.iter().enumerate() {
                if index > 0 {
                    write!(f, ", ")?;
                }
                match argument {
                    Argument::Synthetic => {
                        write!(f, "self: {}", DisplayCallArgumentTypes { types, db, env })?;
                    }
                    Argument::Positional => {
                        write!(f, "{}", DisplayCallArgumentTypes { types, db, env })?;
                    }
                    Argument::Variadic => {
                        write!(f, "*{}", DisplayCallArgumentTypes { types, db, env })?;
                    }
                    Argument::Keyword(name) => write!(
                        f,
                        "{}={}",
                        name,
                        DisplayCallArgumentTypes { types, db, env }
                    )?,
                    Argument::Keywords => {
                        write!(f, "**{}", DisplayCallArgumentTypes { types, db, env })?;
                    }
                }
            }
            f.write_str(")")
        })
    }
}

type TypeExpansion<'db> = Option<Vec<Type<'db>>>;

/// Shares each argument's type expansion between overload checks and argument list expansion.
pub(super) struct CallArgumentExpansions<'s, 'a, 'db> {
    arguments: &'s CallArguments<'a, 'db>,
    db: &'db dyn Db,
    env: &'s ProgramEnvironment<'db>,
    types: OnceCell<Box<[OnceCell<TypeExpansion<'db>>]>>,
}

impl<'a, 'db> CallArgumentExpansions<'_, 'a, 'db> {
    /// Returns the expanded alternatives of an argument, computing them at most once.
    pub(super) fn argument_types(&self, index: usize) -> Option<&[Type<'db>]> {
        // TODO: For types inferred multiple times with distinct type context, we currently only
        // expand the default inference. Note that direct expansion of a type inferred against a
        // given declared type would not likely be assignable to other declared types without
        // re-inference, and so a more complete implementation would likely have to re-infer the
        // argument type against the union a given subset of type contexts before expansion. However,
        // this only shows up in very convoluted instances of generic call inference across multiple
        // overloads, and is unlikely to happen in practice.
        let argument_type = self.arguments.argument_types(index)?.get_default()?;
        // Most calls need no expansion; allocate the cache only when a check asks for it.
        let types = self.types.get_or_init(|| {
            std::iter::repeat_with(OnceCell::new)
                .take(self.arguments.len())
                .collect()
        });
        types[index]
            .get_or_init(|| expand_type(self.db, self.env, argument_type))
            .as_deref()
    }

    /// Whether a starred positional argument can expand into alternative types.
    pub(super) fn has_expandable_variadic(&self) -> bool {
        self.arguments
            .iter()
            .enumerate()
            .any(|(index, (argument, _))| {
                matches!(argument, Argument::Variadic) && self.argument_types(index).is_some()
            })
    }

    /// Iterates over argument lists with successively more argument types expanded.
    ///
    /// See [argument type expansion](https://typing.python.org/en/latest/spec/overload.html#argument-type-expansion).
    pub(super) fn iter(&self) -> impl Iterator<Item = Expansion<'a, 'db>> + '_ {
        /// Represents the state of the expansion process.
        enum State<'a, 'db> {
            LimitReached(usize),
            Expanding(ExpandingState<'a, 'db>),
        }

        /// Represents the expanding state with either the initial types or the expanded types.
        ///
        /// This is useful to avoid cloning the initial types vector if none of the types can be
        /// expanded.
        enum ExpandingState<'a, 'db> {
            Initial,
            Expanded(Vec<CallArguments<'a, 'db>>),
        }

        impl<'a, 'db> ExpandingState<'a, 'db> {
            fn len(&self) -> usize {
                match self {
                    ExpandingState::Initial => 1,
                    ExpandingState::Expanded(expanded) => expanded.len(),
                }
            }

            fn iter<'s>(
                &'s self,
                initial: &'s CallArguments<'a, 'db>,
            ) -> impl Iterator<Item = &'s CallArguments<'a, 'db>> {
                match self {
                    ExpandingState::Initial => Either::Left(std::iter::once(initial)),
                    ExpandingState::Expanded(expanded) => Either::Right(expanded.iter()),
                }
            }
        }

        let mut index = 0;

        std::iter::successors(
            Some(State::Expanding(ExpandingState::Initial)),
            move |previous| {
                let state = match previous {
                    State::LimitReached(index) => return Some(State::LimitReached(*index)),
                    State::Expanding(expanding_state) => expanding_state,
                };

                // Find the next type that can be expanded.
                let expanded_types = loop {
                    self.arguments.argument_types(index)?;
                    if let Some(expanded_types) = self.argument_types(index) {
                        break expanded_types;
                    }
                    index += 1;
                };

                let expansion_size = expanded_types.len() * state.len();
                if expansion_size > MAX_TOTAL_EXPANSION {
                    tracing::debug!(
                        "Skipping argument type expansion as it would exceed the \
                            maximum number of expansions ({MAX_TOTAL_EXPANSION})"
                    );
                    return Some(State::LimitReached(index));
                }

                let mut expanded_arguments = Vec::with_capacity(expansion_size);

                for pre_expanded_types in state.iter(self.arguments) {
                    for subtype in expanded_types {
                        let mut expanded_argument = pre_expanded_types.clone();
                        expanded_argument.items[index].types =
                            CallArgumentTypes::new(Some(*subtype));
                        // Tuple expansion narrows the element types. Dictionary keys are not
                        // represented in their container type and must remain available.
                        if matches!(
                            expanded_argument.items[index].known_unpacking,
                            Some(KnownUnpacking::Positional(_))
                        ) {
                            expanded_argument.items[index].known_unpacking = None;
                        }
                        expanded_arguments.push(expanded_argument);
                    }
                }

                // Increment the index to move to the next argument type for the next iteration.
                index += 1;

                Some(State::Expanding(ExpandingState::Expanded(
                    expanded_arguments,
                )))
            },
        )
        .skip(1) // Skip the initial state, which has no expanded types.
        .map(|state| match state {
            State::LimitReached(index) => Expansion::LimitReached(index),
            State::Expanding(ExpandingState::Initial) => {
                unreachable!("initial state should be skipped")
            }
            State::Expanding(ExpandingState::Expanded(expanded)) => Expansion::Expanded(expanded),
        })
    }
}

/// Represents a single element of the expansion process for argument types for [`CallArgumentExpansions::iter`].
pub(super) enum Expansion<'a, 'db> {
    /// Indicates that the expansion process has reached the maximum number of argument lists
    /// that can be generated in a single step.
    ///
    /// The contained `usize` is the index of the argument type which would have been expanded
    /// next, if not for the limit.
    LimitReached(usize),

    /// Contains the expanded argument lists, where each list contains the same arguments, but with
    /// one or more of the argument types expanded.
    Expanded(Vec<CallArguments<'a, 'db>>),
}

impl<'a, 'db> FromIterator<(Argument<'a>, Option<Type<'db>>)> for CallArguments<'a, 'db> {
    fn from_iter<T>(iter: T) -> Self
    where
        T: IntoIterator<Item = (Argument<'a>, Option<Type<'db>>)>,
    {
        let iter = iter.into_iter();
        let (lower, upper) = iter.size_hint();
        let mut items = Vec::with_capacity(upper.unwrap_or(lower));

        for (argument, ty) in iter {
            items.push(CallArgument {
                argument,
                types: CallArgumentTypes::new(ty),
                known_unpacking: None,
            });
        }

        Self {
            items,
            request_input_proof: false,
        }
    }
}

#[cfg(test)]
mod tests {
    use ruff_db::files::system_path_to_file;
    use ruff_text_size::TextRange;

    use super::*;
    use crate::db::tests::TestDbBuilder;
    use crate::types::call::{Bindings, CallableBinding};
    use crate::types::constraints::ConstraintSetBuilder;
    use crate::types::{KnownClass, Parameter, Signature};

    #[test]
    fn expanded_input_proof_checks_committed_arguments() -> anyhow::Result<()> {
        let db = TestDbBuilder::new().with_file("/src/main.py", "").build()?;
        let file = system_path_to_file(&db, "/src/main.py")?;
        let env = ProgramEnvironment::from_file(db.program_file(file));
        let int = KnownClass::Int.to_instance(&db, &env);
        let object = KnownClass::Object.to_instance(&db, &env);
        let str = KnownClass::Str.to_instance(&db, &env);
        let left = Type::string_literal(&db, "left");
        let right = Type::string_literal(&db, "right");
        let signatures = [left, right].map(|kind| {
            Signature::new(
                Parameters::standard([
                    Parameter::keyword_only(Name::new_static("kind")).with_annotated_type(kind),
                    Parameter::keyword_only(Name::new_static("value")).with_annotated_type(int),
                    Parameter::keyword_only(Name::new_static("tail")).with_annotated_type(int),
                ]),
                Type::none(&db, &env),
            )
        });
        let arguments = CallArguments {
            request_input_proof: true,
            items: vec![
                CallArgument {
                    argument: Argument::Keyword("kind"),
                    types: CallArgumentTypes::new(Some(UnionType::from_two_elements(
                        &db, &env, left, right,
                    ))),
                    known_unpacking: None,
                },
                CallArgument {
                    argument: Argument::Keyword("value"),
                    types: CallArgumentTypes {
                        fallback_type: None,
                        types: [(int, int), (object, int)].into_iter().collect(),
                    },
                    known_unpacking: None,
                },
                CallArgument {
                    argument: Argument::Keywords,
                    types: CallArgumentTypes::new(Some(Type::unknown())),
                    known_unpacking: Some(KnownUnpacking::Keywords(KnownKeywords {
                        items: [DictionaryItem {
                            name: Name::new_static("tail"),
                            ty: int,
                            kind: DictionaryItemKind::Required,
                            source: TextRange::default(),
                        }]
                        .into(),
                        extra_items: None,
                        excluded_names: Vec::new(),
                    })),
                },
            ],
        };
        let bindings = Bindings::from(CallableBinding::from_overloads(Type::unknown(), signatures))
            .match_parameters(&db, &env, &arguments)
            .check_types(
                &db,
                &env,
                &ConstraintSetBuilder::new(),
                &arguments,
                TypeContext::default(),
                &[],
            )
            .map_err(|error| anyhow::anyhow!("{error:?}"))?;
        assert!(bindings.arguments_satisfy_declared_parameters(&db, &env, &arguments));
        assert_eq!(bindings.return_type(&db, &env), Type::none(&db, &env));

        // Committed inference can add a fallback and remove redundant overload contexts.
        let mut committed = arguments.clone();
        committed.items[1].types.fallback_type = Some(int);
        committed.items[1].types.types.remove(&object);
        assert!(bindings.arguments_satisfy_declared_parameters(&db, &env, &committed));

        // The default is unchanged, but an individual context now observes a different type.
        for context in [object, str] {
            let mut changed = committed.clone();
            changed.items[1].types.types.insert(context, str);
            assert_eq!(changed.items[1].types.get_default(), Some(int));
            assert!(!bindings.arguments_satisfy_declared_parameters(&db, &env, &changed));
        }
        for argument in [Argument::Keyword("other"), Argument::Positional] {
            let mut changed = arguments.clone();
            changed.items[1].argument = argument;
            assert!(!bindings.arguments_satisfy_declared_parameters(&db, &env, &changed));
        }
        let mut changed = arguments.clone();
        changed.items.pop();
        assert!(!bindings.arguments_satisfy_declared_parameters(&db, &env, &changed));

        let Some(unpacking) = &arguments.items[2].known_unpacking else {
            anyhow::bail!("expected known unpacked arguments");
        };
        let KnownUnpacking::Keywords(keywords) = unpacking else {
            anyhow::bail!("expected known keyword arguments");
        };
        let mut optional = keywords.clone();
        optional.items[0].kind = DictionaryItemKind::Optional;
        let mut renamed = keywords.clone();
        renamed.items[0].name = Name::new_static("other");
        let mut wrong_value = keywords.clone();
        wrong_value.items[0].ty = str;
        let mut open = keywords.clone();
        open.extra_items = Some(int);
        let mut excluded = keywords.clone();
        excluded.excluded_names.push(Name::new_static("prefix"));
        for keywords in [optional, renamed, wrong_value, open, excluded] {
            let mut changed = arguments.clone();
            changed.items[2].known_unpacking = Some(KnownUnpacking::Keywords(keywords));
            assert!(!bindings.arguments_satisfy_declared_parameters(&db, &env, &changed));
        }
        assert!(
            !CallArgumentTypes::default()
                .has_same_lookups(&CallArgumentTypes::new(Some(Type::unknown())))
        );
        Ok(())
    }

    #[test]
    fn residual_keywords_follow_paramspec_projection() -> anyhow::Result<()> {
        let db = TestDbBuilder::new().with_file("/src/main.py", "").build()?;
        let file = system_path_to_file(&db, "/src/main.py")?;
        let env = ProgramEnvironment::from_file(db.program_file(file));
        let forwarded = Type::string_literal(&db, "forwarded");
        let arguments = CallArguments {
            request_input_proof: false,
            items: vec![CallArgument {
                argument: Argument::Keywords,
                types: CallArgumentTypes::new(Some(Type::unknown())),
                known_unpacking: Some(KnownUnpacking::Keywords(KnownKeywords {
                    items: [
                        DictionaryItem {
                            name: Name::new_static("prefix"),
                            ty: Type::int_literal(1),
                            kind: DictionaryItemKind::Residual,
                            source: TextRange::default(),
                        },
                        DictionaryItem {
                            name: Name::new_static("value"),
                            ty: forwarded,
                            kind: DictionaryItemKind::Residual,
                            source: TextRange::default(),
                        },
                    ]
                    .into(),
                    extra_items: None,
                    excluded_names: Vec::new(),
                })),
            }],
        };
        let parameters =
            Parameters::standard([Parameter::keyword_only(Name::new_static("prefix"))]);
        let projected = arguments.select_for_paramspec(&[0], &parameters, 1);
        let Some(KnownUnpacking::Keywords(keywords)) = projected.known_unpacking(0) else {
            panic!(
                "expected projected keywords, got {:?}",
                projected.known_unpacking(0)
            );
        };
        let values = keywords.residual_values(&db, &env);
        assert_eq!(values, forwarded);
        assert_eq!(keywords.residual_value(&db, None, values), Some(forwarded));
        assert_eq!(
            keywords.residual_value(&db, Some("value"), values),
            Some(forwarded)
        );
        assert_eq!(keywords.residual_value(&db, Some("prefix"), values), None);
        for parameter in [
            Parameter::keyword_only(Name::new_static("value")),
            Parameter::keyword_variadic(Name::new_static("kwargs")),
        ] {
            for (expected, valid) in [(KnownClass::Str, true), (KnownClass::Int, false)] {
                let signature = Signature::new(
                    Parameters::standard([parameter
                        .clone()
                        .with_annotated_type(expected.to_instance(&db, &env))]),
                    Type::none(&db, &env),
                );
                let binding = CallableBinding::from_overloads(Type::unknown(), [signature]);
                let result = Bindings::from(binding)
                    .match_parameters(&db, &env, &projected)
                    .check_types(
                        &db,
                        &env,
                        &ConstraintSetBuilder::new(),
                        &projected,
                        TypeContext::default(),
                        &[],
                    );
                assert_eq!(result.is_ok(), valid, "{parameter:?}: {result:?}");
            }
        }
        Ok(())
    }
}
