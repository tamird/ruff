//! Host-specific Starlark source resolution and syntax admission.

mod analysis;
pub mod bazel;
pub mod graph;
pub mod loads;
pub mod source;
pub mod star;
pub mod stub;

#[cfg(test)]
pub(crate) mod testing;
