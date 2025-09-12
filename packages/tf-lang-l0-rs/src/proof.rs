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

use std::cell::RefCell;
use std::sync::atomic::{AtomicU8, Ordering};

thread_local! {
    static PROOF_LOG: RefCell<Vec<ProofTag>> = RefCell::new(Vec::new());
}

const UNINIT: u8 = 0;
const DISABLED: u8 = 1;
const ENABLED: u8 = 2;
static DEV_PROOFS: AtomicU8 = AtomicU8::new(UNINIT);

pub fn enabled() -> bool {
    match DEV_PROOFS.load(Ordering::Relaxed) {
        ENABLED => true,
        DISABLED => false,
        _ => {
            let val = if std::env::var("DEV_PROOFS").map(|v| v == "1").unwrap_or(false) {
                ENABLED
            } else {
                DISABLED
            };
            DEV_PROOFS.store(val, Ordering::Relaxed);
            val == ENABLED
        }
    }
}

#[doc(hidden)]
pub fn reset() {
    DEV_PROOFS.store(UNINIT, Ordering::Relaxed);
    PROOF_LOG.with(|l| l.borrow_mut().clear());
}

pub fn emit(tag: ProofTag) {
    PROOF_LOG.with(|l| l.borrow_mut().push(tag));
}

pub fn flush() -> Vec<ProofTag> {
    PROOF_LOG.with(|l| l.borrow_mut().drain(..).collect())
}
