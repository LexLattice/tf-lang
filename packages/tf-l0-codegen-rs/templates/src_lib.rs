pub mod adapters;
mod runtime;

pub use adapters::InMemoryAdapters;
pub use runtime::{run_ir, DeterministicClock, TraceRecord, TraceWriter};
