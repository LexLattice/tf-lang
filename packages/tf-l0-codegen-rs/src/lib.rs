use anyhow::{Context, Result};
use serde::ser::Serialize;
use serde_json::Value;
use std::{fs, path::Path};

const TEMPLATE_LIB_RS: &str = include_str!("../templates/src_lib.rs");
const TEMPLATE_PIPELINE_RS: &str = include_str!("../templates/src_pipeline.rs");
const TEMPLATE_ADAPTERS_RS: &str = include_str!("../templates/src_adapters.rs");
const TEMPLATE_RUN_RS: &str = include_str!("../templates/src_bin_run.rs");

pub fn generate_workspace(ir: &Value, out_dir: &Path, package_name: &str) -> Result<()> {
    let src_dir = out_dir.join("src");
    let bin_dir = src_dir.join("bin");

    fs::create_dir_all(&bin_dir).context("creating src/bin directory")?;

    let cargo_toml = render_cargo_toml(package_name);
    fs::write(out_dir.join("Cargo.toml"), cargo_toml).context("writing Cargo.toml")?;

    fs::write(
        out_dir.join("src/lib.rs"),
        ensure_trailing_newline(TEMPLATE_LIB_RS),
    )
    .context("writing src/lib.rs")?;
    fs::write(
        out_dir.join("src/pipeline.rs"),
        ensure_trailing_newline(TEMPLATE_PIPELINE_RS),
    )
    .context("writing src/pipeline.rs")?;
    fs::write(
        out_dir.join("src/adapters.rs"),
        ensure_trailing_newline(TEMPLATE_ADAPTERS_RS),
    )
    .context("writing src/adapters.rs")?;

    let run_rs = ensure_trailing_newline(render_run_rs(package_name));
    fs::write(out_dir.join("src/bin/run.rs"), run_rs).context("writing src/bin/run.rs")?;

    let ir_json = render_ir_json(ir)?;
    fs::write(out_dir.join("ir.json"), ir_json).context("writing ir.json")?;

    Ok(())
}

fn render_cargo_toml(package_name: &str) -> String {
    let mut content = String::new();
    content.push_str("[package]\n");
    content.push_str(&format!("name = \"{package_name}\"\n"));
    content.push_str("version = \"0.1.0\"\n");
    content.push_str("edition = \"2021\"\n");
    content.push_str("license = \"MIT OR Apache-2.0\"\n");
    content.push_str("description = \"Generated TF pipeline\"\n\n");
    content.push_str("[dependencies]\n");
    content.push_str("anyhow = \"1\"\n");
    content.push_str("hex = \"0.4\"\n");
    content.push_str("serde = { version = \"1\", features = [\"derive\"] }\n");
    content.push_str("serde_json = \"1\"\n");
    content.push_str("sha2 = \"0.10\"\n");
    ensure_trailing_newline(content)
}

fn render_run_rs(package_name: &str) -> String {
    TEMPLATE_RUN_RS.replace("__CRATE_NAME__", package_name)
}

fn render_ir_json(ir: &Value) -> Result<String> {
    let canonical = canonicalize_json(ir);
    let mut buf = Vec::new();
    let formatter = serde_json::ser::PrettyFormatter::with_indent(b"  ");
    let mut serializer = serde_json::Serializer::with_formatter(&mut buf, formatter);
    canonical.serialize(&mut serializer)?;
    let mut output = String::from_utf8(buf)?;
    if !output.ends_with('\n') {
        output.push('\n');
    }
    Ok(output)
}

fn canonicalize_json(value: &Value) -> Value {
    match value {
        Value::Object(map) => {
            let mut keys: Vec<_> = map.keys().cloned().collect();
            keys.sort();
            let mut sorted = serde_json::Map::with_capacity(map.len());
            for key in keys {
                let child = map.get(&key).expect("key exists");
                sorted.insert(key, canonicalize_json(child));
            }
            Value::Object(sorted)
        }
        Value::Array(items) => Value::Array(items.iter().map(canonicalize_json).collect()),
        _ => value.clone(),
    }
}

fn ensure_trailing_newline<S: Into<String>>(input: S) -> String {
    let mut content = input.into();
    if !content.ends_with('\n') {
        content.push('\n');
    }
    content
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;
    use std::fs;
    use tempfile::tempdir;

    #[test]
    fn writes_expected_files() {
        let dir = tempdir().unwrap();
        let ir = json!({ "node": "Seq", "children": [] });
        let out_dir = dir.path().join("workspace");
        generate_workspace(&ir, &out_dir, "tf_generated").unwrap();

        let cargo = fs::read_to_string(out_dir.join("Cargo.toml")).unwrap();
        assert!(cargo.contains("serde_json"));
        assert!(out_dir.join("src/lib.rs").exists());
        assert!(out_dir.join("src/pipeline.rs").exists());
        assert!(out_dir.join("src/adapters.rs").exists());
        assert!(out_dir.join("src/bin/run.rs").exists());
        assert!(out_dir.join("ir.json").exists());
    }

    #[test]
    fn render_run_rs_replaces_placeholder() {
        let rendered = render_run_rs("my_crate");
        assert!(rendered.contains("use my_crate::"));
    }
}
