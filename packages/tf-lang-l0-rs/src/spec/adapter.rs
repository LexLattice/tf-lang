use anyhow::{anyhow, Result};
use serde::{Deserialize, Serialize};
use crate::canon::json::canonical_json_bytes;

#[derive(Serialize, Deserialize, Debug, PartialEq, Eq)]
#[serde(tag = "op", content = "params")]
pub enum Step {
    #[serde(rename = "copy")]
    Copy { src: String, dest: String },
    #[serde(rename = "create_network")]
    CreateNetwork { cidr: String },
    #[serde(rename = "create_vm")]
    CreateVm { image: String, cpus: u32 },
}

#[derive(Serialize, Deserialize, Debug, PartialEq, Eq)]
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
    Ok(spec)
}

pub fn serialize_spec(spec: &TfSpec) -> Result<Vec<u8>> {
    let value = serde_json::to_value(spec)?;
    canonical_json_bytes(&value)
}
