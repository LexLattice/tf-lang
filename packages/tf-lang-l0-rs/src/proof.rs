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
pub enum ProofTag {
    Witness { delta: Delta, effect: Effect },
    Normalization { target: NormalizationTarget },
    Transport { op: TransportOp, region: String },
    Refutation { code: String, msg: Option<String> },
    Conservativity { callee: String, expected: String, found: String },
}

use once_cell::sync::Lazy;
use std::sync::Mutex;
use crate::env::dev_proofs_enabled;

pub static PROOF_LOG: Lazy<Mutex<Vec<ProofTag>>> = Lazy::new(|| Mutex::new(Vec::new()));

pub fn emit(tag: ProofTag) {
    if dev_proofs_enabled() {
        PROOF_LOG.lock().unwrap().push(tag);
    }
}

pub fn flush() -> Vec<ProofTag> {
    PROOF_LOG.lock().unwrap().drain(..).collect()
}
