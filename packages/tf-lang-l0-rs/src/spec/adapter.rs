use crate::canon::json::canonical_json_bytes;
use anyhow::{anyhow, Result};
use serde::{Deserialize, Serialize};

#[derive(Serialize, Deserialize, Debug, PartialEq, Eq)]
#[serde(tag = "op", content = "params")]
pub enum Step {
    #[serde(rename = "copy")]
    Copy(CopyParams),
    #[serde(rename = "create_vm")]
    CreateVm(CreateVmParams),
    #[serde(rename = "create_network")]
    CreateNetwork(CreateNetworkParams),
}

#[derive(Serialize, Deserialize, Debug, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
pub struct CopyParams {
    pub src: String,
    pub dest: String,
}

#[derive(Serialize, Deserialize, Debug, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
pub struct CreateVmParams {
    pub image: String,
    pub cpus: u64,
}

#[derive(Serialize, Deserialize, Debug, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
pub struct CreateNetworkParams {
    pub cidr: String,
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
    for step in &spec.steps {
        if let Step::CreateVm(params) = step {
            if params.cpus == 0 {
                return Err(anyhow!("E_CREATE_VM_CPUS"));
            }
        }
    }
    Ok(spec)
}

pub fn serialize_spec(spec: &TfSpec) -> Result<Vec<u8>> {
    let value = serde_json::to_value(spec)?;
    canonical_json_bytes(&value)
}
