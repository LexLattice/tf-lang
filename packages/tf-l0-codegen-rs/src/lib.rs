use anyhow::{Context, Result};
use serde_json::Value;
use std::{collections::BTreeSet, fs, path::Path};

pub trait Network {
    fn publish(&self, topic: &str, key: &str, payload: &str) -> anyhow::Result<()>;
}

pub trait Observability {
    fn emit_metric(&self, name: &str) -> anyhow::Result<()>;
}

pub trait Storage {
    fn write_object(&self, uri: &str, key: &str, value: &str) -> anyhow::Result<()>;
}

pub trait Crypto {
    fn sign(&self, key: &str, data: &[u8]) -> anyhow::Result<Vec<u8>>;
}

pub fn generate_workspace(ir: &Value, out_dir: &Path, package_name: &str) -> Result<()> {
    fs::create_dir_all(out_dir.join("src")).context("creating src directory")?;

    let cargo_toml = render_cargo_toml(package_name);
    fs::write(out_dir.join("Cargo.toml"), cargo_toml).context("writing Cargo.toml")?;

    let pipeline_rs = render_pipeline(ir);
    fs::write(out_dir.join("src/pipeline.rs"), pipeline_rs).context("writing src/pipeline.rs")?;

    let lib_rs = render_lib_rs();
    fs::write(out_dir.join("src/lib.rs"), lib_rs).context("writing src/lib.rs")?;

    Ok(())
}

struct TraitInfo {
    name: &'static str,
    definition: &'static str,
    keywords: &'static [&'static str],
}

static TRAITS: &[TraitInfo] = &[
    TraitInfo {
        name: "Network",
        definition: "pub trait Network {\n    fn publish(&self, topic: &str, key: &str, payload: &str) -> anyhow::Result<()>;\n}\n\n",
        keywords: &["publish"],
    },
    TraitInfo {
        name: "Observability",
        definition: "pub trait Observability {\n    fn emit_metric(&self, name: &str) -> anyhow::Result<()>;\n}\n\n",
        keywords: &["emit-metric"],
    },
    TraitInfo {
        name: "Storage",
        definition: "pub trait Storage {\n    fn write_object(&self, uri: &str, key: &str, value: &str) -> anyhow::Result<()>;\n}\n\n",
        keywords: &["write-object", "delete-object", "compare-and-swap"],
    },
    TraitInfo {
        name: "Crypto",
        definition: "pub trait Crypto {\n    fn sign(&self, key: &str, data: &[u8]) -> anyhow::Result<Vec<u8>>;\n}\n\n",
        keywords: &["sign-data", "verify-signature", "encrypt", "decrypt"],
    },
];

fn render_cargo_toml(package_name: &str) -> String {
    format!(
        "[package]\nname = \"{name}\"\nversion = \"0.1.0\"\nedition = \"2021\"\nlicense = \"MIT OR Apache-2.0\"\ndescription = \"Generated TF pipeline\"\n\n[dependencies]\nanyhow = \"1\"\n",
        name = package_name
    )
}

fn render_lib_rs() -> String {
    "pub mod pipeline;\n\npub use pipeline::run_pipeline;\n".to_string()
}

fn render_pipeline(ir: &Value) -> String {
    let mut traits = BTreeSet::new();
    let mut steps = Vec::new();
    collect_primitives(ir, &mut traits, &mut steps);

    let mut output = String::new();
    output.push_str("use anyhow::Result;\n\n");

    for trait_info in TRAITS {
        output.push_str(trait_info.definition);
    }

    output.push_str("pub fn run_pipeline<A>(adapters: &A) -> Result<()>\nwhere\n    A: ?Sized");
    for name in &traits {
        output.push_str(" + ");
        output.push_str(name);
    }
    output.push_str(",\n{\n");
    output.push_str("    let _ = adapters;\n");

    for step in steps {
        output.push_str("    ");
        output.push_str(&format_step_comment(&step));
        output.push('\n');
    }

    output.push_str("    Ok(())\n}\n");

    output
}

struct StepNote {
    prim: String,
    trait_name: Option<&'static str>,
}

fn format_step_comment(step: &StepNote) -> String {
    match step.trait_name {
        Some(name) => format!("// Prim: {} (requires {})", step.prim, name),
        None => format!("// Prim: {}", step.prim),
    }
}

fn collect_primitives(value: &Value, traits: &mut BTreeSet<&'static str>, steps: &mut Vec<StepNote>) {
    match value {
        Value::Object(map) => {
            let is_prim = matches!(map.get("node"), Some(Value::String(node)) if node == "Prim");
            if is_prim {
                if let Some(Value::String(prim)) = map.get("prim") {
                    if let Some(info) = trait_for_primitive(prim) {
                        traits.insert(info.name);
                        steps.push(StepNote {
                            prim: prim.clone(),
                            trait_name: Some(info.name),
                        });
                    } else {
                        steps.push(StepNote {
                            prim: prim.clone(),
                            trait_name: None,
                        });
                    }
                }
            }

            if let Some(Value::Array(children)) = map.get("children") {
                for child in children {
                    collect_primitives(child, traits, steps);
                }
            }

            let mut keys: Vec<&str> = map
                .keys()
                .map(|key| key.as_str())
                .filter(|key| *key != "children")
                .collect();
            keys.sort_unstable();

            for key in keys {
                if let Some(child) = map.get(key) {
                    collect_primitives(child, traits, steps);
                }
            }
        }
        Value::Array(items) => {
            for item in items {
                collect_primitives(item, traits, steps);
            }
        }
        _ => {}
    }
}

fn trait_for_primitive(name: &str) -> Option<&'static TraitInfo> {
    let base = primitive_base(name);
    let base_lower = base.to_ascii_lowercase();

    TRAITS.iter().find(|info| info.keywords.iter().any(|keyword| *keyword == base_lower))
}

fn primitive_base(name: &str) -> &str {
    let without_suffix = name.split('@').next().unwrap_or(name);
    let mut candidate = without_suffix;
    for delimiter in ['/', '.', ':'] {
        if let Some(index) = candidate.rfind(delimiter) {
            candidate = &candidate[index + 1..];
        }
    }
    candidate
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;

    #[test]
    fn detects_traits_from_mixed_primitives() {
        let ir = json!({
            "node": "Seq",
            "children": [
                {"node": "Prim", "prim": "tf:network/publish@1"},
                {"node": "Prim", "prim": "storage.write-object"},
                {"node": "Prim", "prim": "sign-data"},
                {"node": "Prim", "prim": "emit-metric"}
            ]
        });

        let mut traits = BTreeSet::new();
        let mut steps = Vec::new();
        collect_primitives(&ir, &mut traits, &mut steps);

        let names: Vec<&str> = traits.into_iter().collect();
        assert_eq!(names, vec!["Crypto", "Network", "Observability", "Storage"]);
        assert_eq!(steps.len(), 4);
        assert!(steps.iter().any(|step| step.prim == "tf:network/publish@1"));
    }

    #[test]
    fn primitive_base_handles_compound_names() {
        assert_eq!(primitive_base("tf:network/publish@1"), "publish");
        assert_eq!(primitive_base("storage.write-object"), "write-object");
        assert_eq!(primitive_base("encrypt"), "encrypt");
    }
}
