use anyhow::{anyhow, Result};
use serde::{Deserialize, Serialize};
use serde_json::{Value, Map};
use crate::canon::json::canonical_json_bytes;

#[derive(Serialize, Deserialize, Debug, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
pub struct Step {
    pub op: String,
    pub params: Map<String, Value>,
}

#[derive(Serialize, Deserialize, Debug, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
pub struct TfSpec {
    pub version: String,
    pub name: String,
    pub steps: Vec<Step>,
}

pub fn parse_spec(bytes: &[u8]) -> Result<TfSpec> {
    let spec: TfSpec = serde_json::from_slice(bytes)?;
    if spec.version != "0.1" {
        return Err(anyhow!("E_SPEC_VERSION"));
    }
    if spec.steps.is_empty() {
        return Err(anyhow!("E_SPEC_STEPS"));
    }
    for step in &spec.steps {
        for v in step.params.values() {
            match v {
                Value::String(_) | Value::Number(_) | Value::Bool(_) => {}
                _ => return Err(anyhow!("E_SPEC_PARAM_TYPE")),
            }
        }
    }
    Ok(spec)
}

pub fn serialize_spec(spec: &TfSpec) -> Result<Vec<u8>> {
    let value = serde_json::to_value(spec)?;
    canonical_json_bytes(&value)
}
