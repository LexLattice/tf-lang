use serde::{Deserialize, Serialize};
use serde_json::Value;
use std::sync::{Mutex, OnceLock};
use std::env;

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

static LOG: OnceLock<Mutex<Vec<ProofTag>>> = OnceLock::new();

fn log() -> &'static Mutex<Vec<ProofTag>> {
    LOG.get_or_init(|| Mutex::new(Vec::new()))
}

pub fn emit(tag: ProofTag) {
    if env::var("DEV_PROOFS").ok().as_deref() == Some("1") {
        log().lock().unwrap().push(tag);
    }
}

pub fn take() -> Vec<ProofTag> {
    log().lock().unwrap().drain(..).collect()
}
