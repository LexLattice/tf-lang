#![forbid(unsafe_code)]

//! Helpers for generating Rust scaffolding for Transfer Framework pipelines.

pub mod generate;

pub use generate::{AdapterTrait, GeneratedCrate, PipelineIr};
