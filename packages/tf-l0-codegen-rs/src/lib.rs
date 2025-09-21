use anyhow::{Context, Result};
use serde_json::Value;
use std::{
    fs,
    path::Path,
};

const TEMPLATE_LIB_RS: &str = include_str!("../templates/src_lib.rs");
const TEMPLATE_RUNTIME_RS: &str = include_str!("../templates/src_runtime.rs");
const TEMPLATE_ADAPTERS_RS: &str = include_str!("../templates/src_adapters.rs");
const TEMPLATE_RUN_RS: &str = include_str!("../templates/src_bin_run.rs");

pub fn generate_workspace(ir: &Value, out_dir: &Path, package_name: &str) -> Result<()> {
    let src_dir = out_dir.join("src");
    let bin_dir = src_dir.join("bin");

    fs::create_dir_all(&bin_dir).context("creating src/bin directory")?;

    let cargo_toml = render_cargo_toml(package_name);
    fs::write(out_dir.join("Cargo.toml"), cargo_toml).context("writing Cargo.toml")?;

    fs::write(out_dir.join("src/lib.rs"), TEMPLATE_LIB_RS).context("writing src/lib.rs")?;
    fs::write(out_dir.join("src/runtime.rs"), TEMPLATE_RUNTIME_RS).context("writing src/runtime.rs")?;
    fs::write(out_dir.join("src/adapters.rs"), TEMPLATE_ADAPTERS_RS).context("writing src/adapters.rs")?;

    let run_rs = render_run_rs(package_name);
    fs::write(out_dir.join("src/bin/run.rs"), run_rs).context("writing src/bin/run.rs")?;

    let ir_json = render_ir_json(ir)?;
    fs::write(out_dir.join("ir.json"), ir_json).context("writing ir.json")?;

    Ok(())
}

fn render_cargo_toml(package_name: &str) -> String {
    format!(
        "[package]\nname = \"{name}\"\nversion = \"0.1.0\"\nedition = \"2021\"\nlicense = \"MIT OR Apache-2.0\"\ndescription = \"Generated TF pipeline\"\n\n[dependencies]\nanyhow = \"1\"\nserde = {{ version = \"1\", features = [\"derive\"] }}\nserde_json = \"1\"\nsha2 = \"0.10\"\nhex = \"0.4\"\n",
        name = package_name
    )
}

fn render_run_rs(package_name: &str) -> String {
    TEMPLATE_RUN_RS.replace("__CRATE_NAME__", package_name)
}

fn render_ir_json(ir: &Value) -> Result<String> {
    let serialized = serde_json::to_string_pretty(ir)?;
    Ok(format!("{}\n", serialized))
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
        assert!(out_dir.join("src/runtime.rs").exists());
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
