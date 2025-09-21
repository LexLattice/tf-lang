pub mod adapters;
mod pipeline;

pub use adapters::InMemoryAdapters;
pub use pipeline::{run_ir, DeterministicClock, TraceRecord, TraceWriter};
