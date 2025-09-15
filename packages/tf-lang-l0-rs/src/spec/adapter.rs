use crate::canon::canonical_json_bytes;
use anyhow::Result;
use serde_json::Value;
use std::str;

pub type TfSpec = Value;

pub fn parse_spec(src: &str) -> serde_json::Result<TfSpec> {
    serde_json::from_str(src)
}

pub fn canonical_spec(spec: &TfSpec) -> Result<TfSpec> {
    let bytes = canonical_json_bytes(spec)?;
    let v: TfSpec = serde_json::from_slice(&bytes)?;
    Ok(v)
}

pub fn serialize_spec(spec: &TfSpec) -> Result<String> {
    let bytes = canonical_json_bytes(spec)?;
    Ok(str::from_utf8(&bytes)?.to_string())
}
