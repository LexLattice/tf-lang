use anyhow::{Context, Result};
use serde_json::Value;
use std::{fs, path::Path};

const TEMPLATE_CARGO: &str = include_str!("../templates/Cargo.toml");
const TEMPLATE_LIB: &str = include_str!("../templates/lib.rs");
const TEMPLATE_ADAPTERS: &str = include_str!("../templates/adapters.rs");
const TEMPLATE_PIPELINE: &str = include_str!("../templates/pipeline.rs");
const TEMPLATE_RUN: &str = include_str!("../templates/run.rs");

pub fn generate_workspace(ir: &Value, out_dir: &Path, package_name: &str) -> Result<()> {
    let crate_name = sanitize_crate_name(package_name);
    let src_dir = out_dir.join("src");
    fs::create_dir_all(&src_dir).context("creating src directory")?;

    let cargo_toml = TEMPLATE_CARGO.replace("{{package_name}}", &crate_name);
    fs::write(out_dir.join("Cargo.toml"), ensure_newline(&cargo_toml)).context("writing Cargo.toml")?;

    fs::write(src_dir.join("lib.rs"), ensure_newline(TEMPLATE_LIB)).context("writing src/lib.rs")?;
    fs::write(src_dir.join("adapters.rs"), ensure_newline(TEMPLATE_ADAPTERS))
        .context("writing src/adapters.rs")?;
    fs::write(src_dir.join("pipeline.rs"), ensure_newline(TEMPLATE_PIPELINE))
        .context("writing src/pipeline.rs")?;

    let run_rs = TEMPLATE_RUN.replace("{{crate_name}}", &crate_name);
    fs::write(src_dir.join("run.rs"), ensure_newline(&run_rs)).context("writing src/run.rs")?;

    let ir_json = format!("{}\n", serde_json::to_string_pretty(ir).context("serializing IR")?);
    fs::write(out_dir.join("ir.json"), ir_json).context("writing ir.json")?;

    Ok(())
}

fn ensure_newline(content: &str) -> String {
    if content.ends_with('\n') {
        content.to_string()
    } else {
        format!("{content}\n")
    }
}

fn sanitize_crate_name(value: &str) -> String {
    let lower = value.to_ascii_lowercase();
    let mut out = String::with_capacity(lower.len());
    let mut last_was_underscore = false;

    for ch in lower.chars() {
        let allowed = matches!(ch, 'a'..='z' | '0'..='9' | '_');
        if allowed {
            if ch == '_' {
                if !last_was_underscore {
                    out.push(ch);
                }
                last_was_underscore = true;
            } else {
                out.push(ch);
                last_was_underscore = false;
            }
        } else if !last_was_underscore {
            out.push('_');
            last_was_underscore = true;
        }
    }

    let trimmed = out.trim_matches('_');
    if trimmed.is_empty() {
        "tf_generated".to_string()
    } else {
        trimmed.to_string()
    }
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
        generate_workspace(&ir, dir.path(), "Example-Flow").unwrap();

        let cargo = fs::read_to_string(dir.path().join("Cargo.toml")).unwrap();
        assert!(cargo.contains("name = \"example_flow\""));

        let run = fs::read_to_string(dir.path().join("src/run.rs")).unwrap();
        assert!(run.contains("include_str!(\"../ir.json\")"));

        let ir_json = fs::read_to_string(dir.path().join("ir.json")).unwrap();
        assert!(ir_json.starts_with("{\n"));
        assert!(ir_json.ends_with("\n"));
    }

    #[test]
    fn sanitizes_crate_names() {
        assert_eq!(sanitize_crate_name("My-Crate"), "my_crate");
        assert_eq!(sanitize_crate_name("__"), "tf_generated");
        assert_eq!(sanitize_crate_name("Flow 01"), "flow_01");
    }
}
