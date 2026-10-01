use std::sync::Arc;

use ruff_index::{Idx, IndexVec};
use rustc_hash::{FxHashMap, FxHashSet};
use ty_python_core::rank::{RankBitBox, RankBitBoxVec};

use crate::types::constraints::support::Support;
use crate::types::constraints::variables::{Constraint, ExistentialBound};
use crate::types::constraints::{
    ConstraintId, ConstraintSetStorage, InteriorNode, NodeId, OwnedConstraintSet,
    OwnedConstraintSetInner, SourceOrder, SourceOrderId, SupportId, TypeVarId,
};

pub(super) struct OwnedConstraintSetBuilder {
    used_nodes: RankBitBoxVec,
    used_constraints: RankBitBoxVec,
    used_supports: RankBitBoxVec,
    live_support: Option<Support>,
    source_orders: IndexVec<SourceOrderId, SourceOrder>,
    mapped_source_orders: FxHashMap<SourceOrderId, Option<SourceOrderId>>,
}

impl OwnedConstraintSetBuilder {
    pub(super) fn build(
        storage: ConstraintSetStorage<'_>,
        root: InteriorNode,
        source_order: SourceOrderId,
    ) -> OwnedConstraintSet<'_> {
        let mut builder = Self {
            used_nodes: RankBitBox::bits_with_capacity(storage.nodes.len()),
            used_constraints: RankBitBox::bits_with_capacity(storage.constraints.len()),
            used_supports: RankBitBox::bits_with_capacity(storage.supports.len()),
            live_support: storage.node_support(root.node()).cloned(),
            source_orders: IndexVec::default(),
            mapped_source_orders: FxHashMap::default(),
        };
        builder.mark_node_used(&storage, root.node());
        let mapped_source_order = builder
            .mark_source_order_used(&storage, source_order)
            .expect("non-terminal BDD should have source_order");
        builder.finish(storage, root, mapped_source_order)
    }

    /// Copies the graph reachable from one root without copying the builder's memo tables.
    /// The typevar table stays intact so copied constraints retain their local IDs.
    pub(super) fn snapshot<'db>(
        storage: &ConstraintSetStorage<'db>,
        root: InteriorNode,
        source_order: SourceOrderId,
    ) -> OwnedConstraintSet<'db> {
        let overlay = storage.compacted.as_deref();
        let mut builder = Self {
            used_nodes: RankBitBox::bits_with_capacity(
                storage.nodes.len() + overlay.map_or(0, |inner| inner.node_indices.len()),
            ),
            used_constraints: RankBitBox::bits_with_capacity(
                storage.constraints.len()
                    + overlay.map_or(0, |inner| inner.constraint_indices.len()),
            ),
            used_supports: RankBitBox::bits_with_capacity(
                storage.supports.len() + overlay.map_or(0, |inner| inner.support_indices.len()),
            ),
            live_support: storage.node_support(root.node()).cloned(),
            source_orders: IndexVec::default(),
            mapped_source_orders: FxHashMap::default(),
        };
        builder.mark_node_used(storage, root.node());
        let mapped_source_order = builder
            .mark_source_order_used(storage, source_order)
            .expect("non-terminal BDD should have source_order");
        let nodes = builder
            .used_nodes
            .iter_ones()
            .map(|id| storage.interior_node_data(NodeId::from_usize(id)))
            .collect();
        let node_supports = builder
            .used_nodes
            .iter_ones()
            .map(|id| {
                storage
                    .node_support_id(NodeId::from_usize(id))
                    .expect("marked nodes are nonterminal")
            })
            .collect();
        let constraints = builder
            .used_constraints
            .iter_ones()
            .map(|id| {
                storage
                    .constraint_data(ConstraintId::from_usize(id))
                    .clone()
            })
            .collect();
        let constraint_supports = builder
            .used_constraints
            .iter_ones()
            .map(|id| storage.constraint_support_id(ConstraintId::from_usize(id)))
            .collect();
        let supports = builder
            .used_supports
            .iter_ones()
            .map(|id| storage.support_data(SupportId::from_usize(id)).clone())
            .collect();
        let typevar_count =
            storage.typevars.len() + overlay.map_or(0, |inner| inner.typevars.len());
        let typevars = (0..typevar_count)
            .map(|id| storage.typevar_data(TypeVarId::from_usize(id)))
            .collect();
        builder.finish_parts(
            root,
            mapped_source_order,
            nodes,
            node_supports,
            constraints,
            constraint_supports,
            supports,
            typevars,
        )
    }

    fn mark_node_used(&mut self, storage: &ConstraintSetStorage<'_>, node: NodeId) {
        if node.is_terminal() || self.used_nodes[node.index()] {
            return;
        }
        self.used_nodes.set(node.index(), true);

        let node_support = storage
            .node_support_id(node)
            .expect("node should be non-terminal");
        self.mark_support_used(storage, node_support);

        let interior = storage.interior_node_data(node);
        self.mark_constraint_used(storage, interior.constraint);
        self.mark_node_used(storage, interior.if_true);
        self.mark_node_used(storage, interior.if_uncertain);
        self.mark_node_used(storage, interior.if_false);
    }

    fn mark_constraint_used(
        &mut self,
        storage: &ConstraintSetStorage<'_>,
        constraint: ConstraintId,
    ) {
        if self.used_constraints[constraint.index()] {
            return;
        }
        self.used_constraints.set(constraint.index(), true);

        let constraint_support = storage.constraint_support_id(constraint);
        self.mark_support_used(storage, constraint_support);

        let constraint_data = storage.constraint_data(constraint);
        match constraint_data {
            Constraint::Atomic(_) => {}
            Constraint::Existential(existential) => {
                let ExistentialBound {
                    body,
                    source_order,
                    .. // The constructor marker is private to `variables`.
                } = *existential;
                self.mark_node_used(storage, body);
                if let Some(source_order) = source_order {
                    let mapped_source_order = self.mark_source_order_used(storage, source_order);
                    self.mapped_source_orders
                        .insert(source_order, mapped_source_order);
                }
            }
        }
    }

    fn mark_support_used(&mut self, _storage: &ConstraintSetStorage<'_>, support: SupportId) {
        self.used_supports.set(support.index(), true);
    }

    fn mark_source_order_used(
        &mut self,
        storage: &ConstraintSetStorage<'_>,
        source_order: SourceOrderId,
    ) -> Option<SourceOrderId> {
        // Only first occurrences determine evidence order. Keep quantified constraints as
        // scope markers; their bodies have separate sidecars normalized by mark_constraint_used.
        let mut pending = vec![source_order];
        let mut seen_constraints = FxHashSet::default();
        let mut mapped = None;
        while let Some(current) = pending.pop() {
            match storage.source_order_data(current) {
                SourceOrder::Ordered(left, right) => pending.extend([right, left]),
                SourceOrder::Constraint(constraint) => {
                    // Preserve ordering-only constraints when they share live variables.
                    let constraint_support_id = storage.constraint_support_id(constraint);
                    let constraint_support = storage.support_data(constraint_support_id);
                    if !self.used_constraints[constraint.index()]
                        && let Some(live_support) = self.live_support.as_ref()
                        && live_support.is_complete()
                        && constraint_support.is_complete()
                        && !constraint_support.overlaps_with(live_support)
                    {
                        continue;
                    }
                    if !seen_constraints.insert(constraint) {
                        continue;
                    }
                    self.mark_constraint_used(storage, constraint);
                    self.mark_support_used(storage, constraint_support_id);
                    let next = self.source_orders.push(SourceOrder::Constraint(constraint));
                    mapped = Some(match mapped {
                        None => next,
                        Some(previous) => self
                            .source_orders
                            .push(SourceOrder::Ordered(previous, next)),
                    });
                }
            }
        }
        mapped
    }

    fn finish(
        self,
        storage: ConstraintSetStorage<'_>,
        root: InteriorNode,
        mapped_source_order: SourceOrderId,
    ) -> OwnedConstraintSet<'_> {
        let nodes = storage
            .nodes
            .into_iter()
            .zip(&self.used_nodes)
            .filter_map(|(node, used)| used.then_some(node))
            .collect();
        let node_supports = storage
            .node_supports
            .into_iter()
            .zip(&self.used_nodes)
            .filter_map(|(support, used)| used.then_some(support))
            .collect();

        let constraints = storage
            .constraints
            .into_iter()
            .zip(&self.used_constraints)
            .filter_map(|(constraint, used)| used.then_some(constraint))
            .collect();
        let constraint_supports = storage
            .constraint_supports
            .into_iter()
            .zip(&self.used_constraints)
            .filter_map(|(support, used)| used.then_some(support))
            .collect();

        let supports = storage
            .supports
            .into_iter()
            .zip(&self.used_supports)
            .filter_map(|(support, used)| used.then_some(support))
            .collect();

        self.finish_parts(
            root,
            mapped_source_order,
            nodes,
            node_supports,
            constraints,
            constraint_supports,
            supports,
            storage.typevars,
        )
    }

    #[expect(clippy::too_many_arguments)]
    fn finish_parts<'db>(
        self,
        root: InteriorNode,
        mapped_source_order: SourceOrderId,
        nodes: Box<[super::InteriorNodeData]>,
        node_supports: Box<[SupportId]>,
        mut constraints: Box<[Constraint<'db>]>,
        constraint_supports: Box<[SupportId]>,
        supports: Box<[Support]>,
        mut typevars: IndexVec<TypeVarId, super::BoundTypeVarInstance<'db>>,
    ) -> OwnedConstraintSet<'db> {
        let Self {
            mut used_nodes,
            mut used_constraints,
            mut used_supports,
            live_support: _,
            source_orders,
            mapped_source_orders,
        } = self;
        let largest = used_nodes.last_one().map_or(0, |last| last + 1);
        used_nodes.truncate(largest);
        let largest = used_constraints.last_one().map_or(0, |last| last + 1);
        used_constraints.truncate(largest);
        let largest = used_supports.last_one().map_or(0, |last| last + 1);
        used_supports.truncate(largest);

        for constraint in &mut constraints {
            if let Constraint::Existential(existential) = constraint
                && let Some(source_order) = existential.source_order
            {
                existential.source_order = mapped_source_orders[&source_order];
            }
        }
        let node_indices = RankBitBox::from_bits(used_nodes);
        let constraint_indices = RankBitBox::from_bits(used_constraints);
        let support_indices = RankBitBox::from_bits(used_supports);
        typevars.shrink_to_fit();

        OwnedConstraintSet {
            node: root.node(),
            source_order: Some(mapped_source_order),
            inner: Some(Arc::new(OwnedConstraintSetInner {
                constraints,
                constraint_supports,
                constraint_indices,
                typevars,
                nodes,
                node_supports,
                node_indices,
                supports,
                support_indices,
                source_orders: source_orders.raw.into_boxed_slice(),
            })),
        }
    }
}
