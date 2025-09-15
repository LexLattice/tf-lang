use anyhow::{anyhow, Result};
use serde::{Deserialize, Serialize};
use serde_json::Value;
use crate::canon::json::canonical_json_bytes;

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
pub struct CopyParams {
    pub src: String,
    pub dest: String,
}

#[derive(Serialize, Deserialize, Debug, PartialEq, Eq)]
pub struct CreateVmParams {
    pub image: String,
    pub cpus: u64,
}

#[derive(Serialize, Deserialize, Debug, PartialEq, Eq)]
pub struct CreateNetworkParams {
    pub cidr: String,
}

#[derive(Serialize, Deserialize, Debug, PartialEq, Eq)]
pub struct TfSpec {
    pub version: String,
    pub name: String,
    pub steps: Vec<Step>,
}

pub fn parse_spec(bytes: &[u8]) -> Result<TfSpec> {
    let v: Value = serde_json::from_slice(bytes)?;
    let root = v.as_object().ok_or_else(|| anyhow!("E_SPEC_TYPE /"))?;
    for k in root.keys() {
        if k != "version" && k != "name" && k != "steps" {
            return Err(anyhow!(format!("E_SPEC_FIELD_UNKNOWN {}", k)));
        }
    }
    let version = root
        .get("version")
        .and_then(|v| v.as_str())
        .ok_or_else(|| anyhow!("E_SPEC_VERSION version"))?;
    if version != "0.1" {
        return Err(anyhow!("E_SPEC_VERSION version"));
    }
    let name = root
        .get("name")
        .and_then(|v| v.as_str())
        .ok_or_else(|| anyhow!("E_SPEC_NAME name"))?;
    let steps_val = root
        .get("steps")
        .and_then(|v| v.as_array())
        .ok_or_else(|| anyhow!("E_SPEC_STEPS steps"))?;
    let mut steps = Vec::new();
    for (i, sv) in steps_val.iter().enumerate() {
        let sobj = sv
            .as_object()
            .ok_or_else(|| anyhow!(format!("E_SPEC_STEP steps[{}]", i)))?;
        let op = sobj
            .get("op")
            .and_then(|v| v.as_str())
            .ok_or_else(|| anyhow!(format!("E_SPEC_OP steps[{}].op", i)))?;
        let params = sobj
            .get("params")
            .and_then(|v| v.as_object())
            .ok_or_else(|| anyhow!(format!("E_SPEC_PARAMS steps[{}].params", i)))?;
        let check_keys = |allowed: &[&str]| -> Result<()> {
            for &req in allowed {
                if !params.contains_key(req) {
                    return Err(anyhow!(format!(
                        "E_SPEC_PARAM_MISSING steps[{}].params.{}",
                        i, req
                    )));
                }
            }
            for k in params.keys() {
                if !allowed.contains(&k.as_str()) {
                    return Err(anyhow!(format!(
                        "E_SPEC_PARAM_UNKNOWN steps[{}].params.{}",
                        i, k
                    )));
                }
            }
            Ok(())
        };
        match op {
            "copy" => {
                check_keys(&["src", "dest"])?;
                let src = params
                    .get("src")
                    .and_then(|v| v.as_str())
                    .ok_or_else(|| anyhow!(format!(
                        "E_SPEC_PARAM_TYPE steps[{}].params.src",
                        i
                    )))?;
                let dest = params
                    .get("dest")
                    .and_then(|v| v.as_str())
                    .ok_or_else(|| anyhow!(format!(
                        "E_SPEC_PARAM_TYPE steps[{}].params.dest",
                        i
                    )))?;
                steps.push(Step::Copy(CopyParams {
                    src: src.to_string(),
                    dest: dest.to_string(),
                }));
            }
            "create_vm" => {
                check_keys(&["image", "cpus"])?;
                let image = params
                    .get("image")
                    .and_then(|v| v.as_str())
                    .ok_or_else(|| anyhow!(format!(
                        "E_SPEC_PARAM_TYPE steps[{}].params.image",
                        i
                    )))?;
                let cpus = params
                    .get("cpus")
                    .and_then(|v| v.as_u64())
                    .ok_or_else(|| anyhow!(format!(
                        "E_SPEC_PARAM_TYPE steps[{}].params.cpus",
                        i
                    )))?;
                if cpus < 1 {
                    return Err(anyhow!(format!(
                        "E_SPEC_PARAM_TYPE steps[{}].params.cpus",
                        i
                    )));
                }
                steps.push(Step::CreateVm(CreateVmParams {
                    image: image.to_string(),
                    cpus,
                }));
            }
            "create_network" => {
                check_keys(&["cidr"])?;
                let cidr = params
                    .get("cidr")
                    .and_then(|v| v.as_str())
                    .ok_or_else(|| anyhow!(format!(
                        "E_SPEC_PARAM_TYPE steps[{}].params.cidr",
                        i
                    )))?;
                steps.push(Step::CreateNetwork(CreateNetworkParams {
                    cidr: cidr.to_string(),
                }));
            }
            _ => return Err(anyhow!(format!("E_SPEC_OP_UNKNOWN steps[{}].op", i))),
        }
    }
    Ok(TfSpec {
        version: version.to_string(),
        name: name.to_string(),
        steps,
    })
}

pub fn serialize_spec(spec: &TfSpec) -> Result<Vec<u8>> {
    let value = serde_json::to_value(spec)?;
    canonical_json_bytes(&value)
}
