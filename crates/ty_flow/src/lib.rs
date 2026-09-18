//! Symbolic control-flow constraints and reaching bindings.
//!
//! Callers allocate predicate and definition IDs within a scope, lower their
//! language's control flow, and evaluate predicates using their own type system.
//! Predicate and definition IDs belong to the caller's scope and must agree across
//! its stores. Constraint IDs belong to one builder and its finalized store; they
//! must not cross store boundaries. Finalization retains only roots marked as used
//! and their descendants, preserving their original IDs through compaction.

pub mod bindings;
mod interned_nodes;
pub mod narrowing_constraints;
pub mod predicate;
pub mod rank;
pub mod reachability_constraints;
