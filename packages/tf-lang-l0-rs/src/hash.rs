
use blake3;
use serde::Serialize;

pub fn content_hash(bytes: &[u8]) -> String {
    blake3::hash(bytes).to_hex().to_string()
}

/// NOTE: A placeholder; replace with a canonical JSON encoding if you need bitwise stability
/// across different serde_json versions. Good enough for initial prototyping.
pub fn canonical_json<T: Serialize>(v: &T) -> anyhow::Result<Vec<u8>> {
    let s = serde_json::to_string(v)?;
    Ok(s.into_bytes())
}
