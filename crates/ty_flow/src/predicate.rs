//! Scope-local identifiers for condition atoms.

use ruff_index::Idx;

/// An index into a caller-owned arena of predicates within a scope.
#[derive(Clone, Debug, Copy, PartialOrd, Ord, PartialEq, Eq, Hash, get_size2::GetSize)]
pub struct ScopedPredicateId(u32);

impl ScopedPredicateId {
    /// Identify a predicate in the caller's arena. Terminal IDs are reserved.
    pub const fn from_u32(value: u32) -> Self {
        assert!(value < Self::SMALLEST_TERMINAL.0);
        Self(value)
    }

    pub const fn as_u32(self) -> u32 {
        self.0
    }

    /// A special ID that is used for an "always true" predicate.
    pub const ALWAYS_TRUE: ScopedPredicateId = ScopedPredicateId(0xffff_ffff);

    /// A special ID that is used for an "always false" predicate.
    pub const ALWAYS_FALSE: ScopedPredicateId = ScopedPredicateId(0xffff_fffe);

    const SMALLEST_TERMINAL: ScopedPredicateId = Self::ALWAYS_FALSE;

    pub fn is_terminal(self) -> bool {
        self >= Self::SMALLEST_TERMINAL
    }
}

impl Idx for ScopedPredicateId {
    #[inline]
    fn new(value: usize) -> Self {
        assert!(value <= (Self::SMALLEST_TERMINAL.0 as usize));
        #[expect(clippy::cast_possible_truncation)]
        Self(value as u32)
    }

    #[inline]
    fn index(self) -> usize {
        debug_assert!(!self.is_terminal());
        self.0 as usize
    }
}
