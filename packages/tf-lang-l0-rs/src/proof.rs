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
use std::sync::atomic::{AtomicU8, Ordering};
use std::sync::Mutex;

pub static PROOF_LOG: Lazy<Mutex<Vec<ProofTag>>> = Lazy::new(|| Mutex::new(Vec::new()));

#[repr(u8)]
/// cached DEV_PROOFS state
enum DevFlag {
    /// state not yet read
    Unknown = 0,
    /// env flag evaluated false
    Disabled = 1,
    /// env flag evaluated true
    Enabled = 2,
}

static DEV_PROOFS: AtomicU8 = AtomicU8::new(DevFlag::Unknown as u8);

fn dev_proofs_enabled() -> bool {
    match DEV_PROOFS.load(Ordering::Relaxed) {
        x if x == DevFlag::Enabled as u8 => true,
        x if x == DevFlag::Disabled as u8 => false,
        _ => {
            let val = std::env::var("DEV_PROOFS").ok().as_deref() == Some("1");
            DEV_PROOFS.store(if val { DevFlag::Enabled as u8 } else { DevFlag::Disabled as u8 }, Ordering::Relaxed);
            val
        }
    }
}

pub fn emit(tag: ProofTag) {
    if dev_proofs_enabled() {
        if let Ok(mut log) = PROOF_LOG.lock() {
            log.push(tag);
        } else {
            eprintln!("proof log mutex poisoned");
        }
    }
}

pub fn flush() -> Vec<ProofTag> {
    match PROOF_LOG.lock() {
        Ok(mut log) => log.drain(..).collect(),
        Err(_) => {
            eprintln!("proof log mutex poisoned");
            Vec::new()
        }
    }
}

/// test-only: clear log and env cache
pub fn reset() {
    DEV_PROOFS.store(DevFlag::Unknown as u8, Ordering::Relaxed);
    if let Ok(mut log) = PROOF_LOG.lock() {
        log.clear();
    } else {
        eprintln!("proof log mutex poisoned");
    }
}
