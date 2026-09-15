//! Host-specific Starlark source resolution and syntax admission.

pub mod bazel;
pub mod source;

#[cfg(test)]
pub(crate) mod testing;
