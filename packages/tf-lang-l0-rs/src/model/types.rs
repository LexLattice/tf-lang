
use serde::{Deserialize, Serialize};
use std::collections::{BTreeMap, BTreeSet};

#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq, PartialOrd, Ord)]
pub struct SnapshotId(pub String);

#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq, PartialOrd, Ord)]
pub struct Region(pub String);

#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq, PartialOrd, Ord)]
pub struct Capability(pub String);

#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq, Default)]
pub struct Effects {
    pub reads: BTreeSet<Region>,
    pub writes: BTreeSet<Region>,
}

impl Effects {
    pub fn add_read(&mut self, r: Region) {
        self.reads.insert(r);
    }
    pub fn add_write(&mut self, r: Region) {
        self.writes.insert(r);
    }
    pub fn is_subset_of(&self, other: &Effects) -> bool {
        self.reads.is_subset(&other.reads) && self.writes.is_subset(&other.writes)
    }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Manifest {
    pub tf_id: String,
    pub inputs: Vec<String>,
    pub output: String,
    pub declared_effects: Effects,
    pub bytecode_hash: String,
    pub sig_hash: String,
}

/// Minimal host-independent value space used by the VM.
pub type Value = serde_json::Value;

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct World(pub Value);

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct JournalEntry(pub Value);

/// Convenience “registry” placeholder for TF calls from bytecode.
#[derive(Default)]
pub struct TfRegistry {
    pub funcs: BTreeMap<String, fn(&[Value]) -> anyhow::Result<Value>>,
}

impl TfRegistry {
    pub fn register(mut self, id: &str, f: fn(&[Value]) -> anyhow::Result<Value>) -> Self {
        self.funcs.insert(id.to_string(), f);
        self
    }
    pub fn call(&self, id: &str, args: &[Value]) -> anyhow::Result<Value> {
        self.funcs
            .get(id)
            .ok_or_else(|| anyhow::anyhow!("unknown tf: {}", id))?
            (args)
    }
}
