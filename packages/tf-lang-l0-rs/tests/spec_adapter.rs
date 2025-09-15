use std::fs;
use std::path::PathBuf;
use tflang_l0::spec::adapter::{parse_spec, canonical_spec, serialize_spec};

fn example_paths() -> Vec<PathBuf> {
    let mut dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    dir.pop(); // tf-lang-l0-rs
    dir.pop(); // packages
    dir.push("examples/specs");
    fs::read_dir(dir)
        .unwrap()
        .filter_map(|e| {
            let p = e.ok()?.path();
            if p.extension().and_then(|s| s.to_str()) == Some("json") {
                Some(p)
            } else {
                None
            }
        })
        .collect()
}

#[test]
fn round_trip_examples() -> anyhow::Result<()> {
    for path in example_paths() {
        let src = fs::read_to_string(&path)?;
        let spec = parse_spec(&src)?;
        let canon = canonical_spec(&spec)?;
        let out = serialize_spec(&canon)?;
        let spec2 = parse_spec(&out)?;
        assert_eq!(spec2, canon);
        let out2 = serialize_spec(&spec2)?;
        assert_eq!(out2, out);
    }
    Ok(())
}
