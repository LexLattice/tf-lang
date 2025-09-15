use std::fs;
use std::path::PathBuf;
use serde_json::Value;
use tflang_l0::spec::adapter::{parse_spec, canonical_spec, serialize_spec};
use tflang_l0::canon::canonical_json_bytes;

fn example_dir() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../examples/specs")
}

#[test]
fn round_trip_examples() -> anyhow::Result<()> {
    let dir = example_dir();
    for entry in fs::read_dir(dir)? {
        let entry = entry?;
        if entry.path().extension().and_then(|s| s.to_str()) != Some("json") {
            continue;
        }
        let text = fs::read_to_string(entry.path())?;
        let original: Value = serde_json::from_str(&text)?;
        let spec = canonical_spec(&parse_spec(&original)?);
        let canon = serialize_spec(&spec)?;
        let orig_canon = canonical_json_bytes(&original)?;
        assert_eq!(canon, orig_canon);
    }
    Ok(())
}
