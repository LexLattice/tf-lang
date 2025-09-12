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

#[repr(u8)]
enum DevProofsState {
    Uninit = 0,
    Disabled = 1,
    Enabled = 2,
}

static DEV_PROOFS_STATE: AtomicU8 = AtomicU8::new(DevProofsState::Uninit as u8);

/// Returns true when DEV_PROOFS=1. First call reads the environment and caches
/// the result for subsequent constant-time checks.
pub fn dev_proofs_enabled() -> bool {
    match DEV_PROOFS_STATE.load(Ordering::Relaxed) {
        x if x == DevProofsState::Enabled as u8 => true,
        x if x == DevProofsState::Disabled as u8 => false,
        _ => {
            let enabled = std::env::var("DEV_PROOFS").ok().as_deref() == Some("1");
            DEV_PROOFS_STATE.store(
                if enabled {
                    DevProofsState::Enabled as u8
                } else {
                    DevProofsState::Disabled as u8
                },
                Ordering::Relaxed,
            );
            enabled
        }
    }
}

pub fn emit(tag: ProofTag) {
    if !dev_proofs_enabled() {
        return;
    }
    PROOF_LOG.with(|log| log.borrow_mut().push(tag));
}

pub fn flush() -> Vec<ProofTag> {
    PROOF_LOG.with(|log| log.take())
}

/// Test-only hook: clears cached flag and log so next call re-reads env.
pub fn reset_for_test() {
    DEV_PROOFS_STATE.store(DevProofsState::Uninit as u8, Ordering::Relaxed);
    PROOF_LOG.with(|log| log.borrow_mut().clear());
}
