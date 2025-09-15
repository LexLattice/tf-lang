use std::fs;
use std::path::Path;
use tflang_l0::spec::{parse_spec, serialize_spec};
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
fn reject_wrong_version() {
    let data = br#"{ "version":"0.2","name":"x","steps":[] }"#;
    let err = parse_spec(data).unwrap_err();
    assert_eq!(err.to_string(), "E_SPEC_VERSION");
}

#[test]
fn reject_nested_params() {
    let data = br#"{ "version":"0.1","name":"x","steps":[{"op":"c","params":{"a":{}}}]}"#;
    let err = parse_spec(data).unwrap_err();
    assert_eq!(err.to_string(), "E_SPEC_PARAM_TYPE");
}
