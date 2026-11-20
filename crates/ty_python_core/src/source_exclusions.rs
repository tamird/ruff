//! Frontend syntax that must not contribute Python semantics.

use ruff_text_size::{Ranged, TextRange};

/// Canonical source subtrees omitted by a language frontend.
///
/// Statement roots contribute no definitions or control flow. Their descendants contribute
/// neither bindings nor uses. The ranges must identify complete statement subtrees in the requesting file's parsed revision;
/// they are not diagnostic suppression ranges. Python frontends use the empty default.
#[derive(Clone, Debug, Default, PartialEq, Eq, get_size2::GetSize)]
pub struct SourceExclusions {
    ranges: Box<[TextRange]>,
}

impl SourceExclusions {
    /// The statements must come from the requesting file's canonical parsed revision.
    /// Overlapping subtrees are normalized without merging adjacent statements.
    pub fn from_statements<'a>(
        statements: impl IntoIterator<Item = &'a ruff_python_ast::Stmt>,
    ) -> Self {
        let mut ranges = statements
            .into_iter()
            .map(Ranged::range)
            .collect::<Vec<_>>();
        ranges.sort_unstable_by_key(|range| (range.start(), std::cmp::Reverse(range.end())));
        let mut disjoint: Vec<TextRange> = Vec::with_capacity(ranges.len());
        for range in ranges {
            if let Some(previous) = disjoint.last() {
                if previous.contains_range(range) {
                    continue;
                }
                assert!(
                    previous.end() <= range.start(),
                    "excluded subtrees must be disjoint or nested"
                );
            }
            disjoint.push(range);
        }
        Self {
            ranges: disjoint.into_boxed_slice(),
        }
    }

    /// Whether `range` belongs to an omitted subtree, including its root.
    pub fn contains(&self, range: TextRange) -> bool {
        let end = self
            .ranges
            .partition_point(|excluded| excluded.start() <= range.start());
        end > 0 && self.ranges[end - 1].contains_range(range)
    }
}
