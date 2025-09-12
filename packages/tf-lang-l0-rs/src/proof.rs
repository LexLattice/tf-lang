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
use std::thread_local;

const UNINIT: u8 = 0;
const DISABLED: u8 = 1;
const ENABLED: u8 = 2;

static DEV_PROOFS: AtomicU8 = AtomicU8::new(UNINIT);

fn dev_proofs_enabled() -> bool {
    match DEV_PROOFS.load(Ordering::Relaxed) {
        UNINIT => {
            let val = if std::env::var("DEV_PROOFS").ok().as_deref() == Some("1") {
                ENABLED
            } else {
                DISABLED
            };
            DEV_PROOFS.store(val, Ordering::Relaxed);
            val == ENABLED
        }
        DISABLED => false,
        _ => true,
    }
}

pub fn reset_dev_proofs_for_test() {
    DEV_PROOFS.store(UNINIT, Ordering::Relaxed);
}

thread_local! {
    static LOG: RefCell<Vec<ProofTag>> = RefCell::new(Vec::new());
}

pub fn emit(tag: ProofTag) {
    if dev_proofs_enabled() {
        LOG.with(|log| log.borrow_mut().push(tag));
    }
}

pub fn flush() -> Vec<ProofTag> {
    LOG.with(|log| log.take())
}
