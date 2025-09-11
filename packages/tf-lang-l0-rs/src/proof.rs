use serde::{Deserialize, Serialize};
use serde_json::Value;

#[derive(Clone, Debug, Serialize, Deserialize, PartialEq)]
pub struct Replace {
    pub replace: Value,
}

pub type Delta = Option<Replace>;

#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq, Default)]
pub struct Effect {
    pub read: Vec<String>,
    pub write: Vec<String>,
    pub external: Vec<String>,
}

#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq)]
pub enum NormalizationTarget {
    #[serde(rename = "delta")]
    Delta,
    #[serde(rename = "effect")]
    Effect,
    #[serde(rename = "state")]
    State,
}

#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq)]
pub enum TransportOp {
    #[serde(rename = "LENS_PROJ")]
    LensProj,
    #[serde(rename = "LENS_MERGE")]
    LensMerge,
}

#[derive(Clone, Debug, Serialize, Deserialize, PartialEq)]
#[serde(tag = "kind")]
pub enum Tag {
    Witness { delta: Delta, effect: Effect },
    Normalization { target: NormalizationTarget },
    Transport { op: TransportOp, region: String },
    Refutation { code: String, msg: Option<String> },
    Conservativity { callee: String, expected: String, found: String },
}
