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

use crate::env::dev_proofs_enabled;
use std::cell::RefCell;

thread_local! {
    /// Thread-local proof log to avoid cross-test interference under parallel runs.
    static PROOF_LOG: RefCell<Vec<ProofTag>> = RefCell::new(Vec::new());
}

pub fn emit(tag: ProofTag) {
    if dev_proofs_enabled() {
        PROOF_LOG.with(|log| log.borrow_mut().push(tag));
    }
}

pub fn flush() -> Vec<ProofTag> {
    PROOF_LOG.with(|log| {
        let mut v = log.borrow_mut();
        v.drain(..).collect()
    })
}
