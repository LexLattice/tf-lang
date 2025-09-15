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
pub struct TfSpec {
    pub version: String,
    pub name: String,
    pub steps: Vec<Step>,
}

pub fn parse_spec(bytes: &[u8]) -> Result<TfSpec> {
    let v: Value = serde_json::from_slice(bytes)?;
    let root = v.as_object().ok_or_else(|| anyhow!("E_SPEC_TYPE"))?;
    for k in root.keys() {
        match k.as_str() {
            "version" | "name" | "steps" => {}
            other => return Err(anyhow!("E_SPEC_FIELD: {}", other)),
        }
    }
    let version = root
        .get("version")
        .and_then(Value::as_str)
        .ok_or_else(|| anyhow!("E_SPEC_VERSION"))?;
    if version != "0.1" {
        return Err(anyhow!("E_SPEC_VERSION"));
    }
    let name = root
        .get("name")
        .and_then(Value::as_str)
        .ok_or_else(|| anyhow!("E_SPEC_NAME"))?;
    let steps_v = root
        .get("steps")
        .and_then(Value::as_array)
        .ok_or_else(|| anyhow!("E_SPEC_STEPS"))?;
    let mut steps: Vec<Step> = Vec::new();
    for (i, step_v) in steps_v.iter().enumerate() {
        let step_obj = step_v
            .as_object()
            .ok_or_else(|| anyhow!("E_SPEC_STEP: steps[{}]", i))?;
        for k in step_obj.keys() {
            match k.as_str() {
                "op" | "params" => {}
                other => {
                    return Err(anyhow!(
                        "E_SPEC_STEP_FIELD: steps[{}].{}",
                        i, other
                    ))
                }
            }
        }
        let op = step_obj
            .get("op")
            .and_then(Value::as_str)
            .ok_or_else(|| anyhow!("E_SPEC_OP: steps[{}]", i))?;
        let params_v = step_obj
            .get("params")
            .ok_or_else(|| anyhow!("E_SPEC_PARAMS: steps[{}]", i))?;
        match op {
            "copy" => {
                let params: CopyParams = serde_json::from_value(params_v.clone()).map_err(|e| {
                    let msg = e.to_string();
                    let code = if msg.contains("missing field") {
                        "E_SPEC_PARAM_MISSING"
                    } else if msg.contains("unknown field") {
                        "E_SPEC_PARAM_EXTRA"
                    } else {
                        "E_SPEC_PARAM"
                    };
                    anyhow!("{}: steps[{}].{}", code, i, msg)
                })?;
                steps.push(Step::Copy(params));
            }
            "create_vm" => {
                let params: CreateVmParams = serde_json::from_value(params_v.clone()).map_err(|e| {
                    let msg = e.to_string();
                    let code = if msg.contains("missing field") {
                        "E_SPEC_PARAM_MISSING"
                    } else if msg.contains("unknown field") {
                        "E_SPEC_PARAM_EXTRA"
                    } else {
                        "E_SPEC_PARAM"
                    };
                    anyhow!("{}: steps[{}].{}", code, i, msg)
                })?;
                if params.cpus < 1 {
                    return Err(anyhow!(
                        "E_SPEC_PARAM_INVALID: steps[{}].params.cpus",
                        i
                    ));
                }
                steps.push(Step::CreateVm(params));
            }
            "create_network" => {
                let params: CreateNetworkParams = serde_json::from_value(params_v.clone()).map_err(|e| {
                    let msg = e.to_string();
                    let code = if msg.contains("missing field") {
                        "E_SPEC_PARAM_MISSING"
                    } else if msg.contains("unknown field") {
                        "E_SPEC_PARAM_EXTRA"
                    } else {
                        "E_SPEC_PARAM"
                    };
                    anyhow!("{}: steps[{}].{}", code, i, msg)
                })?;
                steps.push(Step::CreateNetwork(params));
            }
            other => return Err(anyhow!("E_SPEC_OP_UNKNOWN: {}", other)),
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
