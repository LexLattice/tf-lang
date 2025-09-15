use anyhow::Result;
use serde::{Deserialize, Serialize};
use serde_json::Value;
use crate::canon::canonical_json_bytes;

#[derive(Serialize, Deserialize, Debug, PartialEq, Clone)]
pub struct Invariant {
    pub path: String,
    pub equals: Value,
}

#[derive(Serialize, Deserialize, Debug, PartialEq, Clone)]
pub struct Lens {
    pub path: String,
}

#[derive(Serialize, Deserialize, Debug, PartialEq, Clone)]
pub struct TfSpec {
    pub version: String,
    pub goals: Vec<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub invariants: Option<Vec<Invariant>>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub gates: Option<Vec<String>>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub lenses: Option<Vec<Lens>>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub effect: Option<Value>,
}

pub fn parse_spec(v: &Value) -> Result<TfSpec> {
    let spec: TfSpec = serde_json::from_value(v.clone())?;
    Ok(spec)
}

pub fn canonical_spec(spec: &TfSpec) -> TfSpec {
    spec.clone()
}

pub fn serialize_spec(spec: &TfSpec) -> Result<Vec<u8>> {
    let v = serde_json::to_value(spec)?;
    Ok(canonical_json_bytes(&v)?)
}
