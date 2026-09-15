//! Host-specific Starlark source resolution and syntax admission.

pub mod bazel;
pub mod checker;
pub mod preflight;
pub mod source;

#[cfg(test)]
pub(crate) mod testing;
