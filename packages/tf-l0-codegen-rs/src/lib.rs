use anyhow::{Context, Result};
use serde_json::Value;
use std::{collections::BTreeSet, fs, path::Path};

/// Trait requirements exposed by the generated pipeline.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum TraitRequirement {
    Codec,
    Kv,
    Crypto,
    Messaging,
    Metrics,
}

impl TraitRequirement {
    fn name(&self) -> &'static str {
        match self {
            Self::Codec => "Codec",
            Self::Kv => "Kv",
            Self::Crypto => "Crypto",
            Self::Messaging => "Messaging",
            Self::Metrics => "Metrics",
        }
    }

    fn definition(&self) -> &'static str {
        match self {
            Self::Codec => "pub trait Codec {\n    fn serialize(&self, value: &str) -> anyhow::Result<Vec<u8>>;\n    fn deserialize(&self, data: &[u8]) -> anyhow::Result<String>;\n    fn hash(&self, data: &[u8]) -> anyhow::Result<Vec<u8>>;\n}\n",
            Self::Kv => "pub trait Kv {\n    fn write_object(&self, uri: &str, key: &str, value: &str);\n    fn read_object(&self, uri: &str, key: &str) -> Option<String>;\n    fn delete_object(&self, uri: &str, key: &str);\n    fn compare_and_swap(&self, uri: &str, key: &str, expected: &str, value: &str) -> bool;\n}\n",
            Self::Crypto => "pub trait Crypto {\n    fn sign(&self, key: &str, data: &[u8]) -> anyhow::Result<Vec<u8>>;\n    fn verify(&self, key: &str, data: &[u8], signature: &[u8]) -> anyhow::Result<bool>;\n}\n",
            Self::Messaging => "pub trait Messaging {\n    fn publish(&self, topic: &str, payload: &[u8]) -> anyhow::Result<()>;\n    fn request(&self, endpoint: &str, payload: &[u8]) -> anyhow::Result<Vec<u8>>;\n    fn subscribe(&self, topic: &str) -> anyhow::Result<Vec<u8>>;\n    fn acknowledge(&self, token: &str) -> anyhow::Result<()>;\n}\n",
            Self::Metrics => "pub trait Metrics {\n    fn emit_metric(&self, name: &str, value: f64);\n}\n",
        }
    }
}

/// Generate a Rust workspace containing pipeline scaffolding for the provided IR.
pub fn generate_workspace(ir: &Value, out_dir: &Path, package_name: &str) -> Result<()> {
    let traits = infer_traits(ir);
    fs::create_dir_all(out_dir.join("src")).context("creating src directory")?;

    let cargo = render_cargo_toml(package_name);
    fs::write(out_dir.join("Cargo.toml"), cargo).context("writing Cargo.toml")?;

    let lib_rs = render_lib_rs();
    fs::write(out_dir.join("src/lib.rs"), lib_rs).context("writing src/lib.rs")?;

    let pipeline = render_pipeline(&traits);
    fs::write(out_dir.join("src/pipeline.rs"), pipeline).context("writing src/pipeline.rs")?;

    Ok(())
}

fn infer_traits(value: &Value) -> BTreeSet<TraitRequirement> {
    let mut out = BTreeSet::new();
    collect_primitives(value, &mut out);
    out
}

fn collect_primitives(value: &Value, out: &mut BTreeSet<TraitRequirement>) {
    match value {
        Value::Object(map) => {
            if let Some(Value::String(kind)) = map.get("node") {
                if kind == "Prim" {
                    if let Some(Value::String(prim)) = map.get("prim") {
                        if let Some(req) = trait_for_primitive(prim) {
                            out.insert(req);
                        }
                    }
                }
            }
            if let Some(Value::Array(children)) = map.get("children") {
                for child in children {
                    collect_primitives(child, out);
                }
            }
            for (key, value) in map {
                if key != "children" {
                    collect_primitives(value, out);
                }
            }
        }
        Value::Array(items) => {
            for item in items {
                collect_primitives(item, out);
            }
        }
        _ => {}
    }
}

fn trait_for_primitive(name: &str) -> Option<TraitRequirement> {
    match name {
        "serialize" | "deserialize" | "hash" => Some(TraitRequirement::Codec),
        "write-object" | "read-object" | "delete-object" | "compare-and-swap" => {
            Some(TraitRequirement::Kv)
        }
        "sign-data" | "verify-signature" => Some(TraitRequirement::Crypto),
        "publish" | "request" | "subscribe" | "acknowledge" => Some(TraitRequirement::Messaging),
        "emit-metric" => Some(TraitRequirement::Metrics),
        _ => None,
    }
}

fn render_cargo_toml(package_name: &str) -> String {
    format!(
        "[package]\nname = \"{name}\"\nversion = \"0.1.0\"\nedition = \"2021\"\n\n[dependencies]\nanyhow = \"1\"\n\n",
        name = package_name
    )
}

fn render_lib_rs() -> String {
    "pub mod pipeline;\n\npub use pipeline::run_pipeline;\n".to_string()
}

fn render_pipeline(traits: &BTreeSet<TraitRequirement>) -> String {
    let mut sections = String::new();
    for definition in traits.iter().map(TraitRequirement::definition) {
        sections.push_str(definition);
        sections.push('\n');
    }

    if traits.is_empty() {
        sections.push_str("pub trait PipelineAdapters {}\n\nimpl<T> PipelineAdapters for T {}\n");
    }

    let adapter_bounds = if traits.is_empty() {
        "PipelineAdapters".to_string()
    } else {
        traits
            .iter()
            .map(TraitRequirement::name)
            .collect::<Vec<_>>()
            .join(" + ")
    };

    sections.push_str("#[allow(unused_variables)]\n");
    sections.push_str(&format!(
        "pub fn run_pipeline(adapters: &(impl {bounds})) -> anyhow::Result<()> {{\n    let _ = adapters;\n    Ok(())\n}}\n",
        bounds = adapter_bounds
    ));

    sections
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;

    #[test]
    fn infer_traits_from_ir() {
        let ir = json!({
            "node": "Seq",
            "children": [
                {"node": "Prim", "prim": "write-object"},
                {"node": "Prim", "prim": "sign-data"}
            ]
        });

        let traits = infer_traits(&ir);
        assert!(traits.contains(&TraitRequirement::Kv));
        assert!(traits.contains(&TraitRequirement::Crypto));
    }
}
