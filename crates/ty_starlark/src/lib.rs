//! Host-specific Starlark source resolution and syntax admission.

mod analysis;
pub mod bazel;
pub mod checker;
pub mod graph;
mod imports;
pub mod loads;
pub mod overlay;
pub mod preflight;
pub mod source;
pub mod star;
pub mod stub;

#[cfg(test)]
pub(crate) mod testing;
