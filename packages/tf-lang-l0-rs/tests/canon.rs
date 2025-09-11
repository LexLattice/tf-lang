use anyhow::Result;
use serde_json::json;
use tflang_l0::canon::{blake3_hex, canonical_json_bytes};

#[test]
fn sorts_keys_and_preserves_arrays() -> Result<()> {
    let bytes = canonical_json_bytes(&json!({"b":1,"a":[2,1]}))?;
    assert_eq!(String::from_utf8(bytes)?, "{\"a\":[2,1],\"b\":1}");
    Ok(())
}

#[test]
fn rejects_floats() {
    let err = canonical_json_bytes(&json!(1.1)).unwrap_err();
    assert_eq!(err.to_string(), "E_L0_FLOAT");
}

#[test]
fn normalizes_neg_zero() -> Result<()> {
    let a: serde_json::Value = serde_json::from_str("-0")?;
    let b: serde_json::Value = serde_json::from_str("0")?;
    let ca = canonical_json_bytes(&a)?;
    let cb = canonical_json_bytes(&b)?;
    assert_eq!(ca, cb);
    Ok(())
}

#[test]
fn deep_key_ordering() -> Result<()> {
    let a = json!({"x":{"b":1,"a":2},"y":[{"d":4,"c":3}]});
    let b = json!({"y":[{"c":3,"d":4}],"x":{"a":2,"b":1}});
    let ca = canonical_json_bytes(&a)?;
    let cb = canonical_json_bytes(&b)?;
    assert_eq!(ca, cb);
    Ok(())
}

#[test]
fn nested_key_order_in_arrays() -> Result<()> {
    let a = json!({"outer":[{"inner":{"b":1,"a":2}}]});
    let b = json!({"outer":[{"inner":{"a":2,"b":1}}]});
    let ca = canonical_json_bytes(&a)?;
    let cb = canonical_json_bytes(&b)?;
    assert_eq!(ca, cb);
    Ok(())
}

#[test]
fn blake3_hex_empty() {
    let hex = blake3_hex(&[]);
    assert_eq!(
        hex,
        "af1349b9f5f9a1a6a0404dea36dcc9499bcb25c9adc112b7cc9a93cae41f3262"
    );
}
