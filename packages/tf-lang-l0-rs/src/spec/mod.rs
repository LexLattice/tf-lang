use serde::{Deserialize, Serialize};
use serde_json;

#[derive(Serialize, Deserialize, Debug, Clone)]
pub struct Op {
    pub op: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub args: Option<Vec<Op>>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub value: Option<serde_json::Value>,
}

#[derive(Serialize, Deserialize, Debug, Clone)]
pub struct Spec {
    pub version: String,
    pub id: String,
    pub root: Op,
}

pub fn parse(json: &str) -> Result<Spec, serde_json::Error> {
    serde_json::from_str(json)
}

pub fn serialize(spec: &Spec) -> Result<String, serde_json::Error> {
    serde_json::to_string(spec)
}
