use serde_json::Value;
use std::fs;
use std::path::Path;
use tflang_l0::canon::json::canonical_json_bytes;
use tflang_l0::spec::adapter::{parse_spec, serialize_spec};

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
fn parse_errors() {
    let bad_version = br#"{ "version": "0.2", "name": "x", "steps": [] }"#;
    assert!(parse_spec(bad_version).is_err());

    let missing_param = br#"{
        "version": "0.1",
        "name": "x",
        "steps": [ { "op": "copy", "params": { "src": "a" } } ]
    }"#;
    assert!(parse_spec(missing_param).is_err());
}
