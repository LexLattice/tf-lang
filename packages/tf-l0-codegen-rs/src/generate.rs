use serde::Deserialize;
use serde_json::Value;
use std::collections::BTreeSet;
use std::fmt::Write;

/// Representation of the TF pipeline IR that the generator consumes.
#[derive(Debug, Clone, Deserialize)]
pub struct PipelineIr {
    pub node: String,
    #[serde(default)]
    pub prim: Option<String>,
    #[serde(default)]
    pub args: Value,
    #[serde(default)]
    pub meta: Value,
    #[serde(default)]
    pub children: Vec<PipelineIr>,
}

impl PipelineIr {
    /// Returns the canonical pipeline name if present in the metadata.
    pub fn pipeline_name(&self) -> Option<String> {
        pipeline_name_from_meta(&self.meta)
    }

    /// Collects the primitive identifiers referenced by this IR node.
    pub fn primitives(&self) -> BTreeSet<String> {
        let mut out = BTreeSet::new();
        self.collect_primitives(&mut out);
        out
    }

    fn collect_primitives(&self, out: &mut BTreeSet<String>) {
        if self.node == "Prim" {
            if let Some(prim) = &self.prim {
                out.insert(prim.clone());
            }
        }
        for child in &self.children {
            child.collect_primitives(out);
        }
    }
}

fn pipeline_name_from_meta(value: &Value) -> Option<String> {
    match value {
        Value::Null => None,
        Value::String(name) => Some(name.clone()),
        Value::Object(map) => {
            if let Some(Value::String(name)) = map.get("name") {
                if !name.is_empty() {
                    return Some(name.clone());
                }
            }
            if let Some(Value::String(identifier)) = map.get("id") {
                if !identifier.is_empty() {
                    return Some(identifier.clone());
                }
            }
            for key in ["pipeline", "info", "metadata"] {
                if let Some(value) = map.get(key) {
                    if let Some(found) = pipeline_name_from_meta(value) {
                        return Some(found);
                    }
                }
            }
            None
        }
        Value::Array(items) => items.iter().filter_map(pipeline_name_from_meta).next(),
        _ => None,
    }
}

/// The adapter traits that may be required by a generated pipeline.
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum AdapterTrait {
    Kv,
    Crypto,
    Network,
    Observability,
}

impl AdapterTrait {
    /// Returns the trait identifier used in the generated code.
    pub fn as_str(&self) -> &'static str {
        match self {
            AdapterTrait::Kv => "Kv",
            AdapterTrait::Crypto => "Crypto",
            AdapterTrait::Network => "Network",
            AdapterTrait::Observability => "Observability",
        }
    }

    /// Returns the canonical trait definition snippet.
    pub fn definition(&self) -> &'static str {
        match self {
            AdapterTrait::Kv => KV_DEFINITION,
            AdapterTrait::Crypto => CRYPTO_DEFINITION,
            AdapterTrait::Network => NETWORK_DEFINITION,
            AdapterTrait::Observability => OBSERVABILITY_DEFINITION,
        }
    }

    /// Maps a primitive identifier to the adapter trait responsible for it.
    pub fn for_primitive(prim: &str) -> Option<Self> {
        let lower = prim.to_ascii_lowercase();
        if let Some(stripped) = lower.strip_prefix("tf:") {
            if let Some((domain, remainder)) = stripped.split_once('/') {
                let name = remainder.split('@').next().unwrap_or(remainder);
                return match domain {
                    "resource" => Some(AdapterTrait::Kv),
                    "security" => Some(AdapterTrait::Crypto),
                    "network" => Some(AdapterTrait::Network),
                    "observability" => Some(AdapterTrait::Observability),
                    _ => AdapterTrait::from_short_name(name),
                };
            }
        }
        AdapterTrait::from_short_name(lower.as_str())
    }

    fn from_short_name(name: &str) -> Option<Self> {
        match name {
            "write-object" | "read-object" | "delete-object" | "compare-and-swap" => {
                Some(AdapterTrait::Kv)
            }
            "sign-data" | "verify-signature" => Some(AdapterTrait::Crypto),
            "request" | "publish" | "subscribe" | "acknowledge" => Some(AdapterTrait::Network),
            "emit-metric" => Some(AdapterTrait::Observability),
            _ => None,
        }
    }

    pub fn all() -> [AdapterTrait; 4] {
        [
            AdapterTrait::Kv,
            AdapterTrait::Crypto,
            AdapterTrait::Network,
            AdapterTrait::Observability,
        ]
    }
}

/// The fully rendered artifact set for a pipeline crate.
#[derive(Debug, Clone)]
pub struct GeneratedCrate {
    pub crate_name: String,
    pub pipeline_name: String,
    pub traits: BTreeSet<AdapterTrait>,
    pub cargo_toml: String,
    pub lib_rs: String,
    pub pipeline_rs: String,
}

impl GeneratedCrate {
    fn new(
        crate_name: String,
        pipeline_name: String,
        traits: BTreeSet<AdapterTrait>,
        cargo_toml: String,
        lib_rs: String,
        pipeline_rs: String,
    ) -> Self {
        Self {
            crate_name,
            pipeline_name,
            traits,
            cargo_toml,
            lib_rs,
            pipeline_rs,
        }
    }
}

/// Generates the `Cargo.toml`, `lib.rs`, and `pipeline.rs` contents for a pipeline crate.
pub fn generate_crate(ir: &PipelineIr, suggested_crate_name: &str) -> GeneratedCrate {
    let mut traits = BTreeSet::new();
    for prim in ir.primitives() {
        if let Some(adapter) = AdapterTrait::for_primitive(&prim) {
            traits.insert(adapter);
        }
    }

    let crate_name = sanitize_crate_name(suggested_crate_name);
    let pipeline_name = ir
        .pipeline_name()
        .filter(|value| !value.is_empty())
        .unwrap_or_else(|| crate_name.replace('_', "-"));

    let cargo_toml = render_cargo_toml(&crate_name);
    let lib_rs = render_lib_rs();
    let pipeline_rs = render_pipeline_rs(&pipeline_name, &traits);

    GeneratedCrate::new(
        crate_name,
        pipeline_name,
        traits,
        cargo_toml,
        lib_rs,
        pipeline_rs,
    )
}

/// Produces a workspace-safe crate identifier.
pub fn sanitize_crate_name(input: &str) -> String {
    let mut result = String::new();
    let mut last_was_sep = true;
    for ch in input.chars() {
        if ch.is_ascii_alphanumeric() {
            result.push(ch.to_ascii_lowercase());
            last_was_sep = false;
        } else if !last_was_sep && !result.is_empty() {
            result.push('_');
            last_was_sep = true;
        } else {
            last_was_sep = true;
        }
    }
    while result.ends_with('_') {
        result.pop();
    }
    if result.is_empty() {
        result.push_str("pipeline");
    }
    if result
        .chars()
        .next()
        .map(|c| c.is_ascii_digit())
        .unwrap_or(false)
    {
        result.insert_str(0, "pipeline_");
    }
    if matches!(result.as_str(), "crate" | "self" | "super") {
        result.insert_str(0, "pipeline_");
    }
    result
}

fn render_cargo_toml(crate_name: &str) -> String {
    format!(
        "[package]\nname = \"{name}\"\nversion = \"0.1.0\"\nedition = \"2021\"\n\n[dependencies]\nanyhow = \"1.0\"\n",
        name = crate_name
    )
}

fn render_lib_rs() -> String {
    let mut out = String::new();
    out.push_str("#![forbid(unsafe_code)]\n\n");
    out.push_str("pub mod pipeline;\n\n");
    out.push_str("pub use pipeline::run_pipeline;\n");
    out.push_str("pub use pipeline::PipelineAdapters;\n");
    out.push_str("pub use pipeline::PIPELINE_NAME;\n");
    for trait_name in ["Kv", "Crypto", "Network", "Observability"] {
        let _ = writeln!(out, "pub use pipeline::{trait_name};");
    }
    out
}

fn render_pipeline_rs(pipeline_name: &str, traits: &BTreeSet<AdapterTrait>) -> String {
    let mut out = String::new();
    out.push_str("//! Auto-generated pipeline scaffolding.\n\n");
    let _ = writeln!(
        out,
        "pub const PIPELINE_NAME: &str = {};",
        rust_string_literal(pipeline_name)
    );
    out.push('\n');
    for adapter in AdapterTrait::all() {
        out.push_str(adapter.definition());
        out.push('\n');
    }
    let bounds = join_trait_bounds(traits);
    if let Some(bounds) = bounds {
        let _ = writeln!(out, "pub trait PipelineAdapters: {bounds} {{}}\n");
        let _ = writeln!(
            out,
            "impl<T> PipelineAdapters for T where T: {bounds} {{}}\n"
        );
    } else {
        out.push_str("pub trait PipelineAdapters {}\n\n");
        out.push_str("impl<T> PipelineAdapters for T {}\n\n");
    }
    out.push_str("pub fn run_pipeline(adapters: &impl PipelineAdapters) -> anyhow::Result<()> {\n");
    out.push_str("    let _ = adapters;\n");
    out.push_str("    Ok(())\n");
    out.push_str("}\n");
    out
}

fn join_trait_bounds(traits: &BTreeSet<AdapterTrait>) -> Option<String> {
    if traits.is_empty() {
        return None;
    }
    let mut bounds = String::new();
    let mut iter = traits.iter();
    if let Some(first) = iter.next() {
        bounds.push_str(first.as_str());
    }
    for item in iter {
        bounds.push_str(" + ");
        bounds.push_str(item.as_str());
    }
    Some(bounds)
}

fn rust_string_literal(value: &str) -> String {
    let mut escaped = String::with_capacity(value.len() + 2);
    escaped.push('"');
    for ch in value.chars() {
        for escaped_ch in ch.escape_default() {
            escaped.push(escaped_ch);
        }
    }
    escaped.push('"');
    escaped
}

const KV_DEFINITION: &str = r#"pub trait Kv {
    fn write_object(&self, uri: &str, key: &str, value: &str) -> anyhow::Result<()>;
    fn read_object(&self, uri: &str, key: &str) -> anyhow::Result<Option<String>>;
    fn delete_object(&self, uri: &str, key: &str) -> anyhow::Result<()>;
    fn compare_and_swap(
        &self,
        uri: &str,
        key: &str,
        expected: Option<&str>,
        value: &str,
    ) -> anyhow::Result<bool>;
}
"#;

const CRYPTO_DEFINITION: &str = r#"pub trait Crypto {
    fn sign(&self, key: &str, data: &[u8]) -> anyhow::Result<Vec<u8>>;
    fn verify(&self, key: &str, signature: &[u8], data: &[u8]) -> anyhow::Result<bool>;
}
"#;

const NETWORK_DEFINITION: &str = r#"pub trait Network {
    fn request(&self, uri: &str, payload: &[u8]) -> anyhow::Result<Vec<u8>>;
    fn publish(&self, topic: &str, payload: &[u8]) -> anyhow::Result<()>;
    fn subscribe(&self, topic: &str) -> anyhow::Result<()>;
    fn acknowledge(&self, topic: &str, receipt: &str) -> anyhow::Result<()>;
}
"#;

const OBSERVABILITY_DEFINITION: &str = r#"pub trait Observability {
    fn emit_metric(&self, name: &str, value: f64);
}
"#;

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;

    #[test]
    fn generates_scaffolding_for_resource_pipeline() {
        let ir = PipelineIr {
            node: "Prim".into(),
            prim: Some("tf:resource/write-object@1".into()),
            args: Value::Null,
            meta: json!({
                "pipeline": {
                    "name": "Signing",
                }
            }),
            children: vec![],
        };

        let generated = generate_crate(&ir, "Signing-Pipeline");
        assert_eq!(generated.crate_name, "signing_pipeline");
        assert_eq!(generated.pipeline_name, "Signing");
        assert!(generated
            .pipeline_rs
            .contains("pub trait PipelineAdapters: Kv"));
        assert!(generated
            .pipeline_rs
            .contains("pub fn run_pipeline(adapters: &impl PipelineAdapters)"));
    }

    #[test]
    fn falls_back_to_sanitized_name_when_no_metadata() {
        let ir = PipelineIr {
            node: "Seq".into(),
            prim: None,
            args: Value::Null,
            meta: Value::Null,
            children: vec![],
        };

        let generated = generate_crate(&ir, "123 ABC");
        assert_eq!(generated.crate_name, "pipeline_123_abc");
        assert_eq!(generated.pipeline_name, "pipeline-123-abc");
        assert!(generated.pipeline_rs.contains("PIPELINE_NAME"));
    }
}
