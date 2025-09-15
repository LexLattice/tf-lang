use anyhow::Result;
use std::fs;
use std::path::PathBuf;
use serde_json::Value;
use tflang_l0::spec::{parse_spec, serialize_spec};
use tflang_l0::canon::canonical_json_bytes;

#[test]
fn round_trip_examples() -> Result<()> {
    let dir = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../examples/specs");
    for entry in fs::read_dir(dir)? {
        let entry = entry?;
        if !entry.file_name().to_string_lossy().ends_with(".json") {
            continue;
        }
        let data = fs::read(entry.path())?;
        let spec = parse_spec(&data)?;
        let bytes = serialize_spec(&spec)?;
        let orig: Value = serde_json::from_slice(&data)?;
        assert_eq!(bytes, canonical_json_bytes(&orig)?);
        let bytes2 = serialize_spec(&spec)?;
        assert_eq!(bytes, bytes2);
    }
    Ok(())
}
