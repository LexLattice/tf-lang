use std::fs;
use std::path::Path;
use tflang_l0::spec::adapter::{parse_spec, serialize_spec};
use tflang_l0::canon::json::canonical_json_bytes;
use serde_json::Value;

#[test]
fn round_trip_examples() -> anyhow::Result<()> {
    let dir = Path::new("../../examples/specs");
    for entry in fs::read_dir(dir)? {
        let entry = entry?;
        let path = entry.path();
        if path.extension().and_then(|s| s.to_str()) != Some("json") {
            continue;
        }
        let data = fs::read(&path)?;
        let spec = parse_spec(&data)?;
        let out = serialize_spec(&spec)?;
        let expected = canonical_json_bytes(&serde_json::from_slice::<Value>(&data)?)?;
        assert_eq!(out, expected);
    }
    Ok(())
}

#[test]
fn reject_invalid_specs() {
    let bad_op = br#"{ "version": "0.1", "name": "x", "steps": [{"op": "nope", "params": {}}]}"#;
    assert!(parse_spec(bad_op).is_err());
    let missing = br#"{ "version": "0.1", "name": "x", "steps": [{"op": "copy", "params": {"src": "a"}}]}"#;
    assert!(parse_spec(missing).is_err());
}
