use std::fs;
use std::path::Path;
use tflang_l0::spec::{parse, serialize};
use tflang_l0::canon::json::canonical_json_bytes;
use serde_json::from_str;

#[test]
fn test_round_trip_conversion() {
    let examples_dir = Path::new("../../examples/specs");
    for entry in fs::read_dir(examples_dir).unwrap() {
        let entry = entry.unwrap();
        let path = entry.path();
        if path.is_file() && path.extension().and_then(|s| s.to_str()) == Some("json") {
            println!("Testing with file: {:?}", path);
            let original_json = fs::read_to_string(&path).unwrap();
            let spec = parse(&original_json).unwrap();
            let serialized_json = serialize(&spec).unwrap();

            let original_value: serde_json::Value = from_str(&original_json).unwrap();
            let serialized_value: serde_json::Value = from_str(&serialized_json).unwrap();

            let canonical_original = canonical_json_bytes(&original_value).unwrap();
            let canonical_serialized = canonical_json_bytes(&serialized_value).unwrap();

            assert_eq!(
                canonical_serialized,
                canonical_original
            );
        }
    }
}
