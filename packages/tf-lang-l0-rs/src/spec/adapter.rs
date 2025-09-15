use anyhow::{bail, Result};
use serde::{Deserialize, Serialize};
use crate::canon::canonical_json_bytes;

#[derive(Serialize, Deserialize, Debug, PartialEq)]
pub struct Step {
    #[serde(rename = "type")]
    pub step_type: String,
    pub message: String,
}

#[derive(Serialize, Deserialize, Debug, PartialEq)]
pub struct Spec {
    pub version: u32,
    pub description: Option<String>,
    pub steps: Vec<Step>,
}

pub fn parse_spec(bytes: &[u8]) -> Result<Spec> {
    let spec: Spec = serde_json::from_slice(bytes)?;
    if spec.version != 1 {
        bail!("E_SPEC_VERSION");
    }
    for step in &spec.steps {
        if step.step_type != "echo" {
            bail!("E_SPEC_STEP");
        }
    }
    Ok(spec)
}

pub fn serialize_spec(spec: &Spec) -> Result<Vec<u8>> {
    let val = serde_json::to_value(spec)?;
    Ok(canonical_json_bytes(&val)?)
}
