use std::collections::BTreeSet;
use std::fs::{create_dir_all, write};
use std::path::Path;

use anyhow::{anyhow, Context, Result};
use serde_json::{Map, Value};

/// Generate a Rust crate from an IR JSON file located at `ir_path`.
/// Returns the sanitized package name that was written to disk.
pub fn generate_from_ir_path(
    ir_path: impl AsRef<Path>,
    out_dir: impl AsRef<Path>,
    package_name: Option<&str>,
) -> Result<String> {
    let ir_path = ir_path.as_ref();
    let out_dir = out_dir.as_ref();
    let raw = std::fs::read_to_string(ir_path)
        .with_context(|| format!("unable to read IR from {}", ir_path.display()))?;
    let ir: Value = serde_json::from_str(&raw)
        .with_context(|| format!("unable to parse IR from {}", ir_path.display()))?;

    let inferred_name = package_name
        .map(|value| value.to_owned())
        .or_else(|| infer_name_from_ir_path(ir_path))
        .unwrap_or_else(|| "tf_generated".to_string());
    let package = sanitize_package_name(&inferred_name);

    generate_crate(&ir, out_dir, &package)?;
    Ok(package)
}

fn infer_name_from_ir_path(path: &Path) -> Option<String> {
    path.file_stem()
        .and_then(|stem| stem.to_str())
        .map(|stem| stem.trim_end_matches(".ir"))
        .map(|stem| stem.to_string())
}

pub fn sanitize_package_name(name: &str) -> String {
    let mut out = String::new();
    for ch in name.chars() {
        if ch.is_ascii_alphanumeric() {
            out.push(ch.to_ascii_lowercase());
        } else {
            out.push('_');
        }
    }
    if out.is_empty() {
        out.push_str("tf_generated");
    }
    if out
        .chars()
        .next()
        .map(|ch| ch.is_ascii_digit())
        .unwrap_or(false)
    {
        out.insert(0, '_');
    }
    out
}

fn generate_crate(ir: &Value, out_dir: &Path, package_name: &str) -> Result<()> {
    let node = parse_node(ir)?;
    let traits = collect_traits(&node);
    let pipeline = render_pipeline(&node, &traits)?;
    let lib_rs = render_library();
    let cargo_toml = render_cargo_toml(package_name);

    let src_dir = out_dir.join("src");
    create_dir_all(&src_dir).with_context(|| format!("creating {}", src_dir.display()))?;

    write(out_dir.join("Cargo.toml"), cargo_toml)
        .with_context(|| format!("writing {}/Cargo.toml", out_dir.display()))?;
    write(src_dir.join("lib.rs"), lib_rs)
        .with_context(|| format!("writing {}/src/lib.rs", out_dir.display()))?;
    write(src_dir.join("pipeline.rs"), pipeline)
        .with_context(|| format!("writing {}/src/pipeline.rs", out_dir.display()))?;
    Ok(())
}

#[derive(Debug, Clone)]
enum Node {
    Prim {
        prim: String,
        args: Map<String, Value>,
    },
    Seq {
        children: Vec<Node>,
    },
    Par {
        children: Vec<Node>,
    },
    Region {
        children: Vec<Node>,
    },
}

fn parse_node(value: &Value) -> Result<Node> {
    let obj = value
        .as_object()
        .ok_or_else(|| anyhow!("IR node must be an object"))?;
    let node_type = obj
        .get("node")
        .and_then(|value| value.as_str())
        .ok_or_else(|| anyhow!("IR node missing `node` type"))?;
    match node_type {
        "Prim" => {
            let prim = obj
                .get("prim")
                .and_then(|value| value.as_str())
                .ok_or_else(|| anyhow!("Prim node missing `prim`"))?;
            let args = obj
                .get("args")
                .and_then(|value| value.as_object())
                .map(|map| map.clone())
                .unwrap_or_default();
            Ok(Node::Prim {
                prim: prim.to_string(),
                args,
            })
        }
        "Seq" | "Par" | "Region" => {
            let children = obj
                .get("children")
                .and_then(|value| value.as_array())
                .ok_or_else(|| anyhow!("{} node missing `children`", node_type))?;
            let mut parsed = Vec::with_capacity(children.len());
            for child in children {
                parsed.push(parse_node(child)?);
            }
            match node_type {
                "Seq" => Ok(Node::Seq { children: parsed }),
                "Par" => Ok(Node::Par { children: parsed }),
                "Region" => Ok(Node::Region { children: parsed }),
                _ => unreachable!(),
            }
        }
        other => Err(anyhow!("unsupported IR node type `{}`", other)),
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum TraitKind {
    Codec,
    Hasher,
    Crypto,
    Kv,
    Messaging,
    Metrics,
}

fn collect_traits(node: &Node) -> BTreeSet<TraitKind> {
    let mut traits = BTreeSet::new();
    collect_traits_inner(node, &mut traits);
    traits
}

fn collect_traits_inner(node: &Node, traits: &mut BTreeSet<TraitKind>) {
    match node {
        Node::Prim { prim, .. } => {
            traits.extend(required_traits_for_prim(prim));
        }
        Node::Seq { children } | Node::Par { children } | Node::Region { children, .. } => {
            for child in children {
                collect_traits_inner(child, traits);
            }
        }
    }
}

fn required_traits_for_prim(prim: &str) -> Vec<TraitKind> {
    match prim {
        "serialize" | "deserialize" | "transform" => vec![TraitKind::Codec],
        "hash" => vec![TraitKind::Hasher],
        "sign-data" | "verify-signature" => vec![TraitKind::Crypto],
        "write-object" | "read-object" | "delete-object" | "compare-and-swap" => {
            vec![TraitKind::Kv]
        }
        "publish" | "request" | "subscribe" | "acknowledge" => vec![TraitKind::Messaging],
        "emit-metric" => vec![TraitKind::Metrics],
        _ => Vec::new(),
    }
}

fn render_cargo_toml(package_name: &str) -> String {
    format!(
        "[package]\nname = \"{name}\"\nversion = \"0.1.0\"\nedition = \"2021\"\n\n[dependencies]\nanyhow = \"1\"\nserde_json = \"1\"\n",
        name = package_name,
    )
}

fn render_library() -> String {
    r#"use anyhow::Result;
use serde_json::{Map, Value};

pub mod pipeline;

pub trait Kv {
    fn write_object(&self, uri: &str, key: &str, value: &str) -> Result<()>;
    fn read_object(&self, uri: &str, key: &str) -> Result<Option<String>>;
    fn delete_object(&self, uri: &str, key: &str) -> Result<()>;
    fn compare_and_swap(
        &self,
        uri: &str,
        key: &str,
        expected: Option<&[u8]>,
        value: &[u8],
    ) -> Result<bool>;
}

pub trait Crypto {
    fn sign(&self, key_ref: &str, data: &[u8]) -> Result<Vec<u8>>;
    fn verify(&self, key_ref: &str, data: &[u8], signature: &[u8]) -> Result<bool>;
}

pub trait Codec {
    fn serialize(&self, value: &Value) -> Result<Vec<u8>>;
    fn deserialize(&self, data: &[u8]) -> Result<Value>;
    fn transform(
        &self,
        function: &str,
        value: &Value,
        args: &Map<String, Value>,
    ) -> Result<Value>;
}

pub trait Hasher {
    fn hash(&self, data: &[u8]) -> Result<Vec<u8>>;
}

pub trait Messaging {
    fn publish(&self, topic: &str, key: Option<&str>, payload: &str) -> Result<()>;
    fn request(&self, topic: &str, payload: &str) -> Result<String>;
    fn subscribe(&self, topic: &str) -> Result<()>;
    fn acknowledge(&self, subscription: &str, message_id: &str) -> Result<()>;
}

pub trait Metrics {
    fn emit_metric(&self, name: &str) -> Result<()>;
}

pub use pipeline::run_pipeline;
"#
    .to_string()
}

fn render_pipeline(node: &Node, traits: &BTreeSet<TraitKind>) -> Result<String> {
    let adapter_sig = if traits.is_empty() {
        "impl crate::Codec".to_string()
    } else {
        format!(
            "impl {}",
            traits
                .iter()
                .map(|kind| kind.trait_name())
                .collect::<Vec<_>>()
                .join(" + ")
        )
    };

    let mut state = RenderState::new(adapter_sig);
    let root_fn = state.render_node(node)?;

    let mut output = String::new();
    if !traits.is_empty() {
        output.push_str("use crate::{");
        let list = traits
            .iter()
            .map(|kind| kind.trait_name())
            .collect::<Vec<_>>()
            .join(", ");
        output.push_str(&list);
        output.push_str("};\n\n");
    }
    output.push_str(&format!(
        "pub fn run_pipeline(adapters: &({})) -> anyhow::Result<()> {{\n    {}(adapters)\n}}\n\n",
        state.adapter_sig, root_fn
    ));

    for function in state.functions {
        output.push_str(&function);
        output.push('\n');
    }

    Ok(output)
}

struct RenderState {
    adapter_sig: String,
    functions: Vec<String>,
    next_id: usize,
}

impl RenderState {
    fn new(adapter_sig: String) -> Self {
        Self {
            adapter_sig,
            functions: Vec::new(),
            next_id: 0,
        }
    }

    fn render_node(&mut self, node: &Node) -> Result<String> {
        match node {
            Node::Prim { prim, args } => self.render_prim(prim, args),
            Node::Seq { children } => self.render_sequence("seq", children),
            Node::Par { children } => self.render_parallel(children),
            Node::Region { children } => self.render_sequence("region", children),
        }
    }

    fn render_sequence(&mut self, prefix: &str, children: &[Node]) -> Result<String> {
        let fn_name = self.next_function_name(prefix);
        let mut body = String::new();
        for child in children {
            let child_fn = self.render_node(child)?;
            body.push_str(&format!("    {}(adapters)?;\n", child_fn));
        }
        body.push_str("    Ok(())\n");
        let function = format!(
            "fn {name}(adapters: &({sig})) -> anyhow::Result<()> {{\n{body}}}\n",
            name = &fn_name,
            sig = &self.adapter_sig,
            body = body
        );
        self.functions.push(function);
        Ok(fn_name)
    }

    fn render_parallel(&mut self, children: &[Node]) -> Result<String> {
        let fn_name = self.next_function_name("par");
        let mut body = String::new();
        body.push_str("    // TODO: execute in parallel\n");
        for child in children {
            let child_fn = self.render_node(child)?;
            body.push_str(&format!("    {}(adapters)?;\n", child_fn));
        }
        body.push_str("    Ok(())\n");
        let function = format!(
            "fn {name}(adapters: &({sig})) -> anyhow::Result<()> {{\n{body}}}\n",
            name = &fn_name,
            sig = &self.adapter_sig,
            body = body
        );
        self.functions.push(function);
        Ok(fn_name)
    }

    fn render_prim(&mut self, prim: &str, args: &Map<String, Value>) -> Result<String> {
        let fn_name = self.next_function_name("prim");
        let statements = render_prim_statements(prim, args);
        let mut body = String::new();
        for line in statements {
            body.push_str("    ");
            body.push_str(&line);
            if !line.ends_with('\n') {
                body.push('\n');
            }
        }
        body.push_str("    Ok(())\n");
        let function = format!(
            "fn {name}(adapters: &({sig})) -> anyhow::Result<()> {{\n{body}}}\n",
            name = &fn_name,
            sig = &self.adapter_sig,
            body = body
        );
        self.functions.push(function);
        Ok(fn_name)
    }

    fn next_function_name(&mut self, prefix: &str) -> String {
        let name = format!("{}_{}", prefix, self.next_id);
        self.next_id += 1;
        name
    }
}

impl TraitKind {
    fn trait_name(&self) -> &'static str {
        match self {
            TraitKind::Codec => "Codec",
            TraitKind::Hasher => "Hasher",
            TraitKind::Crypto => "Crypto",
            TraitKind::Kv => "Kv",
            TraitKind::Messaging => "Messaging",
            TraitKind::Metrics => "Metrics",
        }
    }
}

fn render_prim_statements(prim: &str, args: &Map<String, Value>) -> Vec<String> {
    match prim {
        "serialize" => vec![
            "let _ = adapters.serialize(&serde_json::Value::Null)?; // TODO: provide input".to_string(),
        ],
        "deserialize" => vec![
            "let _ = adapters.deserialize(&[])?; // TODO: provide bytes".to_string(),
        ],
        "transform" => vec![
            format!(
                "let _ = adapters.transform({}, todo!(\"value\"), todo!(\"args\"))?;",
                string_arg(args, "fn").unwrap_or_else(|| "todo!(\"function\")".to_string())
            ),
        ],
        "hash" => vec!["let _ = adapters.hash(&[])?; // TODO: provide input".to_string()],
        "sign-data" => vec![format!(
            "let _ = adapters.sign({}, &[])?; // TODO: provide payload",
            string_arg(args, "key_ref").unwrap_or_else(|| "todo!(\"key_ref\")".to_string())
        )],
        "verify-signature" => vec![format!(
            "let _ = adapters.verify({}, &[], &[])?; // TODO: provide payload and signature",
            string_arg(args, "key_ref").unwrap_or_else(|| "todo!(\"key_ref\")".to_string())
        )],
        "write-object" => vec![format!(
            "adapters.write_object({}, {}, {})?;",
            string_arg(args, "uri").unwrap_or_else(|| "todo!(\"uri\")".to_string()),
            string_arg(args, "key").unwrap_or_else(|| "todo!(\"key\")".to_string()),
            string_arg(args, "value").unwrap_or_else(|| "todo!(\"value\")".to_string())
        )],
        "read-object" => vec![format!(
            "let _ = adapters.read_object({}, {})?;",
            string_arg(args, "uri").unwrap_or_else(|| "todo!(\"uri\")".to_string()),
            string_arg(args, "key").unwrap_or_else(|| "todo!(\"key\")".to_string())
        )],
        "delete-object" => vec![format!(
            "adapters.delete_object({}, {})?;",
            string_arg(args, "uri").unwrap_or_else(|| "todo!(\"uri\")".to_string()),
            string_arg(args, "key").unwrap_or_else(|| "todo!(\"key\")".to_string())
        )],
        "compare-and-swap" => vec![format!(
            "let _ = adapters.compare_and_swap({}, {}, None, &[])?; // TODO: supply compare-and-swap payload",
            string_arg(args, "uri").unwrap_or_else(|| "todo!(\"uri\")".to_string()),
            string_arg(args, "key").unwrap_or_else(|| "todo!(\"key\")".to_string())
        )],
        "publish" => vec![format!(
            "adapters.publish({}, {}, {})?;",
            string_arg(args, "topic").unwrap_or_else(|| "todo!(\"topic\")".to_string()),
            optional_string_arg(args, "key"),
            string_arg(args, "payload").unwrap_or_else(|| "todo!(\"payload\")".to_string())
        )],
        "request" => vec![format!(
            "let _ = adapters.request({}, {})?;",
            string_arg(args, "topic").unwrap_or_else(|| "todo!(\"topic\")".to_string()),
            string_arg(args, "payload").unwrap_or_else(|| "todo!(\"payload\")".to_string())
        )],
        "subscribe" => vec![format!(
            "adapters.subscribe({})?;",
            string_arg(args, "topic").unwrap_or_else(|| "todo!(\"topic\")".to_string())
        )],
        "acknowledge" => vec![format!(
            "adapters.acknowledge({}, {})?;",
            string_arg(args, "subscription").unwrap_or_else(|| "todo!(\"subscription\")".to_string()),
            string_arg(args, "message_id").unwrap_or_else(|| "todo!(\"message_id\")".to_string())
        )],
        "emit-metric" => vec![format!(
            "adapters.emit_metric({})?;",
            string_arg(args, "name").unwrap_or_else(|| "todo!(\"name\")".to_string())
        )],
        other => vec![format!(
            "anyhow::bail!(\"primitive {name} is not yet supported\");",
            name = other
        )],
    }
}

fn string_arg(args: &Map<String, Value>, key: &str) -> Option<String> {
    args.get(key)
        .and_then(|value| value.as_str())
        .map(|value| format!("{:?}", value))
}

fn optional_string_arg(args: &Map<String, Value>, key: &str) -> String {
    match string_arg(args, key) {
        Some(value) => format!("Some({})", value),
        None => "None".to_string(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn sanitize_produces_valid_name() {
        assert_eq!(sanitize_package_name("Signing"), "signing");
        assert_eq!(sanitize_package_name("123name"), "_123name");
        assert_eq!(sanitize_package_name("na-me"), "na_me");
    }
}
