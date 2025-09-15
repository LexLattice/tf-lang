pub mod canon;
pub mod check;
pub mod model;
pub mod spec;
pub mod util;
pub mod vm;
pub mod ops;
pub mod proof;

// Avoid glob re-exports at crate root to prevent ambiguous names (e.g., `types`).
