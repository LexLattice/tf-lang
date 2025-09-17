use std::collections::BTreeMap;
use std::fs;
use std::path::Path;

use serde::{Deserialize, Serialize};
use serde_json::{Map, Value};
use thiserror::Error;

#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq)]
pub struct Spec {
    pub version: String,
    pub name: String,
    #[serde(default)]
    pub steps: Vec<Step>,
}

#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq)]
pub struct Step {
    pub op: String,
    #[serde(default)]
    pub params: BTreeMap<String, Value>,
}

#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq)]
pub struct TraceSpec {
    pub name: String,
    pub version: String,
}

#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq)]
pub struct TraceEvent {
    #[serde(rename = "stepIndex")]
    pub step_index: usize,
    pub op: String,
    pub outcome: String,
    pub params: Value,
    pub details: Value,
}

#[derive(Clone, Debug, Default, Serialize, Deserialize, PartialEq, Eq)]
pub struct CopySummary {
    pub src: String,
    pub dest: String,
}

#[derive(Clone, Debug, Default, Serialize, Deserialize, PartialEq, Eq)]
pub struct VmSummary {
    pub id: String,
    pub image: String,
    pub cpus: i64,
}

#[derive(Clone, Debug, Default, Serialize, Deserialize, PartialEq, Eq)]
pub struct NetworkSummary {
    pub id: String,
    pub cidr: String,
}

#[derive(Clone, Debug, Default, Serialize, Deserialize, PartialEq, Eq)]
pub struct ResourceSummary {
    pub copies: Vec<CopySummary>,
    pub vms: Vec<VmSummary>,
    pub networks: Vec<NetworkSummary>,
}

#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq)]
pub struct ExecutionTrace {
    pub spec: TraceSpec,
    pub events: Vec<TraceEvent>,
    pub summary: ResourceSummary,
}

#[derive(Debug, Error, Clone, PartialEq, Eq)]
pub enum AdapterError {
    #[error("E_ADAPTER_UNKNOWN_OP {op}")]
    UnknownOp { op: String },
    #[error("E_ADAPTER_PARAM {op} {param}")]
    InvalidParam { op: String, param: String },
    #[error("E_ADAPTER_IO {path}")]
    Io { path: String },
    #[error("E_ADAPTER_PARSE {0}")]
    Parse(String),
}

pub type Result<T> = std::result::Result<T, AdapterError>;

pub fn execute(spec: &Spec) -> Result<ExecutionTrace> {
    let mut events = Vec::with_capacity(spec.steps.len());
    let mut summary = ResourceSummary::default();
    let mut vm_counter = 0i64;
    let mut network_counter = 0i64;

    for (index, step) in spec.steps.iter().enumerate() {
        match step.op.as_str() {
            "copy" => {
                let src = string_param(step, "src")?;
                let dest = string_param(step, "dest")?;
                let params = sorted_object([
                    ("src", Value::String(src.clone())),
                    ("dest", Value::String(dest.clone())),
                ]);
                let details = params.clone();
                events.push(TraceEvent {
                    step_index: index,
                    op: step.op.clone(),
                    outcome: "success".to_string(),
                    params,
                    details,
                });
                summary.copies.push(CopySummary { src, dest });
            }
            "create_vm" => {
                vm_counter += 1;
                let image = string_param(step, "image")?;
                let cpus = int_param(step, "cpus")?;
                let id = format!("vm-{vm_counter}");
                let params = sorted_object([
                    ("image", Value::String(image.clone())),
                    ("cpus", Value::Number(cpus.into())),
                ]);
                let details = sorted_object([
                    ("id", Value::String(id.clone())),
                    ("image", Value::String(image.clone())),
                    ("cpus", Value::Number(cpus.into())),
                ]);
                events.push(TraceEvent {
                    step_index: index,
                    op: step.op.clone(),
                    outcome: "success".to_string(),
                    params,
                    details,
                });
                summary.vms.push(VmSummary { id, image, cpus });
            }
            "create_network" => {
                network_counter += 1;
                let cidr = string_param(step, "cidr")?;
                let id = format!("net-{network_counter}");
                let params = sorted_object([("cidr", Value::String(cidr.clone()))]);
                let details = sorted_object([
                    ("id", Value::String(id.clone())),
                    ("cidr", Value::String(cidr.clone())),
                ]);
                events.push(TraceEvent {
                    step_index: index,
                    op: step.op.clone(),
                    outcome: "success".to_string(),
                    params,
                    details,
                });
                summary.networks.push(NetworkSummary { id, cidr });
            }
            other => {
                return Err(AdapterError::UnknownOp {
                    op: other.to_string(),
                })
            }
        }
    }

    Ok(ExecutionTrace {
        spec: TraceSpec {
            name: spec.name.clone(),
            version: spec.version.clone(),
        },
        events,
        summary,
    })
}

fn string_param(step: &Step, key: &str) -> Result<String> {
    match step.params.get(key) {
        Some(Value::String(value)) => Ok(value.clone()),
        _ => Err(AdapterError::InvalidParam {
            op: step.op.clone(),
            param: key.to_string(),
        }),
    }
}

fn int_param(step: &Step, key: &str) -> Result<i64> {
    match step.params.get(key) {
        Some(Value::Number(num)) => num.as_i64().ok_or_else(|| AdapterError::InvalidParam {
            op: step.op.clone(),
            param: key.to_string(),
        }),
        _ => Err(AdapterError::InvalidParam {
            op: step.op.clone(),
            param: key.to_string(),
        }),
    }
}

fn sorted_object<const N: usize>(pairs: [(&str, Value); N]) -> Value {
    let mut tree = BTreeMap::new();
    for (key, value) in pairs {
        tree.insert(key.to_string(), value);
    }
    Value::Object(tree.into_iter().collect::<Map<String, Value>>())
}

pub fn load_spec(path: &Path) -> Result<Spec> {
    let data = fs::read_to_string(path).map_err(|_| AdapterError::Io {
        path: path.display().to_string(),
    })?;
    serde_json::from_str(&data).map_err(|err| AdapterError::Parse(err.to_string()))
}

pub fn write_trace(path: &Path, trace: &ExecutionTrace) -> Result<()> {
    let json =
        serde_json::to_string_pretty(trace).map_err(|err| AdapterError::Parse(err.to_string()))?;
    if let Some(parent) = path.parent() {
        fs::create_dir_all(parent).map_err(|_| AdapterError::Io {
            path: parent.display().to_string(),
        })?;
    }
    fs::write(path, format!("{json}\n")).map_err(|_| AdapterError::Io {
        path: path.display().to_string(),
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn fixture(name: &str) -> &'static str {
        match name {
            "spec" => include_str!("../fixtures/sample-spec.json"),
            "trace" => include_str!("../fixtures/sample-trace.json"),
            _ => panic!("unknown fixture"),
        }
    }

    #[test]
    fn executes_spec() {
        let spec: Spec = serde_json::from_str(fixture("spec")).expect("spec");
        let trace = execute(&spec).expect("trace");
        let expected: ExecutionTrace = serde_json::from_str(fixture("trace")).expect("trace");
        assert_eq!(trace, expected);
    }

    #[test]
    fn rejects_unknown_ops() {
        let mut spec: Spec = serde_json::from_str(fixture("spec")).expect("spec");
        spec.steps.push(Step {
            op: "noop".into(),
            params: BTreeMap::new(),
        });
        let err = execute(&spec).expect_err("must fail");
        assert!(matches!(err, AdapterError::UnknownOp { .. }));
    }
}
