
use crate::model::{JournalEntry, Value, World};

/// Host trait: domain hooks the VM calls for non-pure core ops.
pub trait Host {
    fn lens_project(&self, state: &Value, region: &str) -> anyhow::Result<Value>;
    fn lens_merge(&self, state: &Value, region: &str, substate: &Value) -> anyhow::Result<Value>;

    fn snapshot_make(&self, state: &Value) -> anyhow::Result<Value>;
    fn snapshot_id(&self, snapshot: &Value) -> anyhow::Result<String>;

    fn diff_apply(&self, state: &Value, delta: &Value) -> anyhow::Result<Value>;
    fn diff_invert(&self, delta: &Value) -> anyhow::Result<Value>;

    fn journal_record(&self, plan: &Value, delta: &Value, s0: &str, s1: &str, meta: &Value) -> anyhow::Result<JournalEntry>;
    fn journal_rewind(&self, world: &World, entry: &JournalEntry) -> anyhow::Result<World>;

    /// Generic TF call boundary (pure, content-addressed).
    fn call_tf(&self, tf_id: &str, args: &[Value]) -> anyhow::Result<Value>;
}
