pub mod canon;
pub mod check;
pub mod model;
pub mod util;
pub mod vm;
pub mod ops;
pub mod proof;
pub mod proof_macro;
pub mod spec;

// Avoid glob re-exports at crate root to prevent ambiguous names (e.g., `types`).
