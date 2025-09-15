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
    let root: Value = serde_json::from_slice(bytes)?;
    let obj = root.as_object().ok_or_else(|| anyhow!("E_SPEC_TYPE /"))?;
    let version = obj
        .get("version")
        .and_then(Value::as_str)
        .ok_or_else(|| anyhow!("E_SPEC_VERSION /version"))?;
    if version != "0.1" {
        return Err(anyhow!("E_SPEC_VERSION /version"));
    }
    let name = obj
        .get("name")
        .and_then(Value::as_str)
        .ok_or_else(|| anyhow!("E_SPEC_NAME /name"))?
        .to_string();
    let steps_val = obj.get("steps").ok_or_else(|| anyhow!("E_SPEC_STEPS /steps"))?;
    let steps_arr = steps_val.as_array().ok_or_else(|| anyhow!("E_SPEC_STEPS /steps"))?;
    let mut steps: Vec<Step> = Vec::new();
    for (i, s_val) in steps_arr.iter().enumerate() {
        let s_obj = s_val
            .as_object()
            .ok_or_else(|| anyhow!(format!("E_SPEC_STEP /steps/{i}")))?;
        if s_obj.len() != 2 {
            return Err(anyhow!(format!("E_SPEC_STEP /steps/{i}")));
        }
        let op = s_obj
            .get("op")
            .and_then(Value::as_str)
            .ok_or_else(|| anyhow!(format!("E_SPEC_OP /steps/{i}/op")))?;
        let params_val = s_obj
            .get("params")
            .and_then(Value::as_object)
            .ok_or_else(|| anyhow!(format!("E_SPEC_PARAMS /steps/{i}/params")))?;
        let step = match op {
            "copy" => {
                let src = params_val
                    .get("src")
                    .and_then(Value::as_str)
                    .ok_or_else(|| anyhow!(format!("E_SPEC_PARAM /steps/{i}/params/src")))?;
                let dest = params_val
                    .get("dest")
                    .and_then(Value::as_str)
                    .ok_or_else(|| anyhow!(format!("E_SPEC_PARAM /steps/{i}/params/dest")))?;
                if params_val.len() != 2 {
                    return Err(anyhow!(format!("E_SPEC_PARAM /steps/{i}/params")));
                }
                Step::Copy(CopyParams {
                    src: src.to_string(),
                    dest: dest.to_string(),
                })
            }
            "create_vm" => {
                let image = params_val
                    .get("image")
                    .and_then(Value::as_str)
                    .ok_or_else(|| anyhow!(format!("E_SPEC_PARAM /steps/{i}/params/image")))?;
                let cpus = params_val
                    .get("cpus")
                    .and_then(Value::as_u64)
                    .filter(|c| *c >= 1)
                    .ok_or_else(|| anyhow!(format!("E_SPEC_PARAM /steps/{i}/params/cpus")))?;
                if params_val.len() != 2 {
                    return Err(anyhow!(format!("E_SPEC_PARAM /steps/{i}/params")));
                }
                Step::CreateVm(CreateVmParams {
                    image: image.to_string(),
                    cpus,
                })
            }
            "create_network" => {
                let cidr = params_val
                    .get("cidr")
                    .and_then(Value::as_str)
                    .ok_or_else(|| anyhow!(format!("E_SPEC_PARAM /steps/{i}/params/cidr")))?;
                if params_val.len() != 1 {
                    return Err(anyhow!(format!("E_SPEC_PARAM /steps/{i}/params")));
                }
                Step::CreateNetwork(CreateNetworkParams {
                    cidr: cidr.to_string(),
                })
            }
            _ => return Err(anyhow!(format!("E_SPEC_OP_UNKNOWN /steps/{i}/op"))),
        };
        steps.push(step);
    }
    Ok(TfSpec {
        version: version.to_string(),
        name,
        steps,
    })
}

pub fn serialize_spec(spec: &TfSpec) -> Result<Vec<u8>> {
    let value = serde_json::to_value(spec)?;
    canonical_json_bytes(&value)
}
