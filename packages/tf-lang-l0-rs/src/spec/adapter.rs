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

fn err(code: &str, path: &str, msg: &str) -> anyhow::Error {
    anyhow!("{} at {}: {}", code, path, msg)
}

pub fn parse_spec(bytes: &[u8]) -> Result<TfSpec> {
    let v: Value = serde_json::from_slice(bytes)?;
    if !v.is_object() {
        return Err(err("E_SPEC_TYPE", "", "spec must be an object"));
    }
    let root = v.as_object().unwrap();
    let allowed_root = ["version", "name", "steps"];
    for k in root.keys() {
        if !allowed_root.contains(&k.as_str()) {
            return Err(err("E_SPEC_EXTRA", k, "unexpected field"));
        }
    }
    let version = match root.get("version") {
        Some(Value::String(s)) if s == "0.1" => s.clone(),
        Some(_) => return Err(err("E_SPEC_VERSION", "version", "expected \"0.1\"")),
        None => return Err(err("E_SPEC_VERSION", "version", "missing")),
    };
    let name = match root.get("name") {
        Some(Value::String(s)) => s.clone(),
        Some(_) => return Err(err("E_SPEC_NAME", "name", "must be string")),
        None => return Err(err("E_SPEC_NAME", "name", "missing")),
    };
    let steps_v = match root.get("steps") {
        Some(Value::Array(a)) => a,
        Some(_) => return Err(err("E_SPEC_STEPS", "steps", "must be array")),
        None => return Err(err("E_SPEC_STEPS", "steps", "missing")),
    };
    let mut steps = Vec::new();
    for (i, s) in steps_v.iter().enumerate() {
        let spath = format!("steps[{}]", i);
        if !s.is_object() {
            return Err(err("E_SPEC_STEP", &spath, "must be object"));
        }
        let step_obj = s.as_object().unwrap();
        for k in step_obj.keys() {
            if k != "op" && k != "params" {
                return Err(err("E_SPEC_EXTRA", &format!("{}.{k}", spath), "unexpected field"));
            }
        }
        let op_v = step_obj.get("op").ok_or_else(|| err("E_SPEC_OP", &format!("{}.op", spath), "missing"))?;
        let op = op_v.as_str().ok_or_else(|| err("E_SPEC_OP", &format!("{}.op", spath), "must be string"))?;
        let params_v = step_obj.get("params").ok_or_else(|| err("E_SPEC_PARAMS", &format!("{}.params", spath), "missing"))?;
        if !params_v.is_object() {
            return Err(err("E_SPEC_PARAMS", &format!("{}.params", spath), "must be object"));
        }
        let params = params_v.as_object().unwrap();
        match op {
            "copy" => {
                let src = match params.get("src") {
                    Some(Value::String(s)) => s.clone(),
                    _ => return Err(err("E_SPEC_PARAM", &format!("{}.params.src", spath), "must be string")),
                };
                let dest = match params.get("dest") {
                    Some(Value::String(s)) => s.clone(),
                    _ => return Err(err("E_SPEC_PARAM", &format!("{}.params.dest", spath), "must be string")),
                };
                for k in params.keys() {
                    if k != "src" && k != "dest" {
                        return Err(err("E_SPEC_PARAM", &format!("{}.params.{}", spath, k), "unexpected param"));
                    }
                }
                steps.push(Step::Copy(CopyParams { src, dest }));
            }
            "create_vm" => {
                let image = match params.get("image") {
                    Some(Value::String(s)) => s.clone(),
                    _ => return Err(err("E_SPEC_PARAM", &format!("{}.params.image", spath), "must be string")),
                };
                let cpus_v = params.get("cpus").ok_or_else(|| err("E_SPEC_PARAM", &format!("{}.params.cpus", spath), "must be integer >=1"))?;
                let cpus = cpus_v.as_i64().or_else(|| cpus_v.as_u64().map(|u| u as i64)).ok_or_else(|| err("E_SPEC_PARAM", &format!("{}.params.cpus", spath), "must be integer >=1"))?;
                if cpus < 1 {
                    return Err(err("E_SPEC_PARAM", &format!("{}.params.cpus", spath), "must be integer >=1"));
                }
                for k in params.keys() {
                    if k != "image" && k != "cpus" {
                        return Err(err("E_SPEC_PARAM", &format!("{}.params.{}", spath, k), "unexpected param"));
                    }
                }
                steps.push(Step::CreateVm(CreateVmParams { image, cpus: cpus as u64 }));
            }
            "create_network" => {
                let cidr = match params.get("cidr") {
                    Some(Value::String(s)) => s.clone(),
                    _ => return Err(err("E_SPEC_PARAM", &format!("{}.params.cidr", spath), "must be string")),
                };
                for k in params.keys() {
                    if k != "cidr" {
                        return Err(err("E_SPEC_PARAM", &format!("{}.params.{}", spath, k), "unexpected param"));
                    }
                }
                steps.push(Step::CreateNetwork(CreateNetworkParams { cidr }));
            }
            _ => {
                return Err(err("E_SPEC_OP_UNKNOWN", &format!("{}.op", spath), &format!("unknown op {}", op)));
            }
        }
    }
    Ok(TfSpec { version, name, steps })
}

pub fn serialize_spec(spec: &TfSpec) -> Result<Vec<u8>> {
    let value = serde_json::to_value(spec)?;
    canonical_json_bytes(&value)
}
