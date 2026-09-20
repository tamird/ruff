use std::any::Any;
use std::fmt::Debug;
use std::hash::{Hash, Hasher};
use std::sync::Arc;

/// Immutable application data attached to a synthesized class.
///
/// This data cannot contain database-borrowed types. Field types and callable signatures belong
/// in the ordinary type graph, where Ty can visit and normalize them. Equality is by value,
/// including the concrete Rust type; pointer identity does not affect query results.
#[derive(Clone, Debug, salsa::SalsaValue)]
pub struct ProvidedData(Arc<dyn Data>);

trait Data: Debug + Send + Sync {
    fn as_any(&self) -> &dyn Any;
    fn eq(&self, other: &dyn Any) -> bool;
    fn hash(&self, state: &mut dyn Hasher);
    fn heap_size(&self) -> usize;
}

impl<T: Any + Debug + Eq + Hash + Send + Sync + get_size2::GetSize> Data for T {
    fn as_any(&self) -> &dyn Any {
        self
    }
    fn eq(&self, other: &dyn Any) -> bool {
        other.downcast_ref::<T>() == Some(self)
    }
    fn hash(&self, mut state: &mut dyn Hasher) {
        self.type_id().hash(&mut state);
        Hash::hash(self, &mut state);
    }
    fn heap_size(&self) -> usize {
        self.get_size()
    }
}

impl ProvidedData {
    pub fn new<T: Any + Debug + Eq + Hash + Send + Sync + get_size2::GetSize>(value: T) -> Self {
        Self(Arc::new(value))
    }

    pub fn downcast_ref<T: Any>(&self) -> Option<&T> {
        self.0.as_any().downcast_ref()
    }
}

impl PartialEq for ProvidedData {
    fn eq(&self, other: &Self) -> bool {
        self.0.eq(other.0.as_any())
    }
}
impl Eq for ProvidedData {}
impl Hash for ProvidedData {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.0.hash(state);
    }
}
impl get_size2::GetSize for ProvidedData {
    fn get_heap_size(&self) -> usize {
        self.0.heap_size()
    }
}
