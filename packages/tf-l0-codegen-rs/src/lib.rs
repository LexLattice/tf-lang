use std::collections::BTreeSet;
use std::fs::{create_dir_all, write};
use std::path::Path;

use anyhow::{Context, Result};
use serde::Deserialize;

const PIPELINE_TEMPLATE: &str = include_str!("templates/pipeline.rs.hbs");

pub fn emit_workspace(ir: &Node, out_dir: &Path) -> Result<()> {
    let src_dir = out_dir.join("src");
    create_dir_all(&src_dir).with_context(|| format!("unable to create {}", display(&src_dir)))?;

    let cargo_toml = render_cargo_toml(out_dir);
    write(out_dir.join("Cargo.toml"), cargo_toml)
        .with_context(|| format!("unable to write Cargo.toml in {}", display(out_dir)))?;

    write(src_dir.join("lib.rs"), render_lib_rs())
        .with_context(|| format!("unable to write lib.rs in {}", display(&src_dir)))?;

    let pipeline = render_pipeline_rs(ir);
    write(src_dir.join("pipeline.rs"), pipeline)
        .with_context(|| format!("unable to write pipeline.rs in {}", display(&src_dir)))?;

    Ok(())
}

fn render_cargo_toml(out_dir: &Path) -> String {
    let package_name = normalize_crate_name(out_dir);
    format!(
        "[package]\nname = \"{}\"\nversion = \"0.1.0\"\nedition = \"2021\"\n\n[dependencies]\nanyhow = \"1\"\nserde_json = \"1\"\n",
        package_name
    )
}

fn render_lib_rs() -> &'static str {
    "pub mod pipeline;\n\npub use pipeline::*;\n"
}

fn render_pipeline_rs(ir: &Node) -> String {
    let traits = required_traits(ir);
    let trait_bounds = if traits.is_empty() {
        "PipelineBase".to_string()
    } else {
        traits
            .iter()
            .map(TraitKind::name)
            .collect::<Vec<_>>()
            .join(" + ")
    };

    let tree = describe(ir);
    let steps = if tree.is_empty() {
        "    // No operations were inferred from the IR.\n".to_string()
    } else {
        let mut buf = String::from("    // Pipeline skeleton inferred from the IR:\n");
        for line in tree {
            buf.push_str("    // ");
            buf.push_str(&line);
            buf.push('\n');
        }
        buf
    };

    PIPELINE_TEMPLATE
        .replace("{{TRAIT_BOUNDS}}", &trait_bounds)
        .replace("{{STEPS}}", &steps)
        .replace("{{TRAITS}}", TRAIT_DEFINITIONS)
}

fn required_traits(root: &Node) -> BTreeSet<TraitKind> {
    let mut traits = BTreeSet::new();
    root.walk(&mut |node| {
        if let Node::Prim { prim, prim_id, .. } = node {
            if let Some(name) = prim
                .as_ref()
                .map(|s| s.as_str())
                .or_else(|| prim_id.as_deref())
            {
                if let Some(kind) = TraitKind::from_primitive(name) {
                    traits.insert(kind);
                }
            }
        }
    });
    traits
}

fn describe(root: &Node) -> Vec<String> {
    let mut lines = Vec::new();
    root.walk_with_depth(0, &mut |node, depth| match node {
        Node::Prim { prim, prim_id, .. } => {
            let name = prim
                .as_deref()
                .map(str::to_owned)
                .or_else(|| prim_id.as_deref().map(trim_prim_id))
                .unwrap_or_else(|| "unknown-prim".to_string());
            lines.push(format!("{}- prim: {}", indent(depth), name));
        }
        Node::Seq { .. } => {
            lines.push(format!("{}- seq", indent(depth)));
        }
        Node::Par { .. } => {
            lines.push(format!("{}- par", indent(depth)));
        }
        Node::Region { kind, .. } => {
            let label = kind.clone().unwrap_or_else(|| "region".to_string());
            lines.push(format!("{}- region: {}", indent(depth), label));
        }
        Node::Other => {
            lines.push(format!("{}- unknown node", indent(depth)));
        }
    });
    lines
}

fn indent(depth: usize) -> String {
    "  ".repeat(depth)
}

fn trim_prim_id(id: &str) -> String {
    let tail = id.rsplit_once('/').map(|(_, tail)| tail).unwrap_or(id);
    let tail = tail.split('@').next().unwrap_or(tail);
    tail.to_string()
}

fn normalize_crate_name(out_dir: &Path) -> String {
    let fallback = "tf_generated";
    let raw = out_dir
        .file_name()
        .and_then(|s| s.to_str())
        .unwrap_or(fallback);
    let mut slug = String::new();
    for ch in raw.chars() {
        if ch.is_ascii_alphanumeric() {
            slug.push(ch.to_ascii_lowercase());
        } else if !slug.ends_with('_') {
            slug.push('_');
        }
    }
    while slug.starts_with('_') {
        slug.remove(0);
    }
    if slug.is_empty() {
        slug = fallback.to_string();
    }
    if !slug
        .chars()
        .next()
        .map(|c| c.is_ascii_lowercase())
        .unwrap_or(false)
    {
        slug = format!("tf_{}", slug);
    }
    slug
}

fn display(path: &Path) -> String {
    path.to_string_lossy().into_owned()
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum TraitKind {
    Codec,
    Crypto,
    Hasher,
    Kv,
    Network,
    Observability,
}

impl TraitKind {
    fn name(&self) -> &'static str {
        match self {
            TraitKind::Codec => "Codec",
            TraitKind::Crypto => "Crypto",
            TraitKind::Hasher => "Hasher",
            TraitKind::Kv => "Kv",
            TraitKind::Network => "Network",
            TraitKind::Observability => "Observability",
        }
    }

    fn from_primitive(name: &str) -> Option<Self> {
        let key = trim_prim_id(name);
        match key.as_str() {
            "serialize" | "deserialize" => Some(TraitKind::Codec),
            "hash" => Some(TraitKind::Hasher),
            "sign-data" | "verify-signature" => Some(TraitKind::Crypto),
            "write-object" | "read-object" | "delete-object" | "compare-and-swap" => {
                Some(TraitKind::Kv)
            }
            "publish" | "subscribe" | "request" | "acknowledge" => Some(TraitKind::Network),
            "emit-metric" => Some(TraitKind::Observability),
            _ => None,
        }
    }
}

static TRAIT_DEFINITIONS: &str = r#"pub trait PipelineBase {}
impl<T> PipelineBase for T {}

pub trait Kv {
    fn write_object(&self, uri: &str, key: &str, value: &str) -> Result<()>;
    fn read_object(&self, uri: &str, key: &str) -> Result<Option<String>>;
    fn delete_object(&self, uri: &str, key: &str) -> Result<()>;
    fn compare_and_swap(&self, uri: &str, key: &str, expected: &str, value: &str) -> Result<bool>;
}

pub trait Crypto {
    fn sign(&self, key: &str, data: &[u8]) -> Result<Vec<u8>>;
    fn verify(&self, key: &str, data: &[u8], signature: &[u8]) -> Result<bool>;
}

pub trait Codec {
    fn serialize(&self, value: &serde_json::Value) -> Result<Vec<u8>>;
    fn deserialize(&self, bytes: &[u8]) -> Result<serde_json::Value>;
}

pub trait Hasher {
    fn hash(&self, value: &serde_json::Value) -> Result<String>;
}

pub trait Network {
    fn request(&self, route: &str, payload: &serde_json::Value) -> Result<serde_json::Value>;
    fn publish(&self, topic: &str, payload: &serde_json::Value) -> Result<()>;
    fn subscribe(&self, topic: &str) -> Result<Vec<serde_json::Value>>;
    fn acknowledge(&self, topic: &str, message_id: &str) -> Result<()>;
}

pub trait Observability {
    fn emit_metric(&self, name: &str, value: f64);
}
"#;

#[derive(Debug, Deserialize)]
#[serde(tag = "node")]
pub enum Node {
    #[serde(rename = "Prim")]
    Prim {
        #[serde(default)]
        prim: Option<String>,
        #[serde(default)]
        prim_id: Option<String>,
        #[serde(default)]
        children: Vec<Node>,
    },
    #[serde(rename = "Seq")]
    Seq {
        #[serde(default)]
        children: Vec<Node>,
    },
    #[serde(rename = "Par")]
    Par {
        #[serde(default)]
        children: Vec<Node>,
    },
    #[serde(rename = "Region")]
    Region {
        #[serde(default)]
        kind: Option<String>,
        #[serde(default)]
        children: Vec<Node>,
    },
    #[serde(other)]
    Other,
}

impl Node {
    fn walk<F>(&self, f: &mut F)
    where
        F: FnMut(&Node),
    {
        f(self);
        for child in self.children() {
            child.walk(f);
        }
    }

    fn walk_with_depth<F>(&self, depth: usize, f: &mut F)
    where
        F: FnMut(&Node, usize),
    {
        f(self, depth);
        for child in self.children() {
            child.walk_with_depth(depth + 1, f);
        }
    }

    fn children(&self) -> &[Node] {
        match self {
            Node::Prim { children, .. }
            | Node::Seq { children }
            | Node::Par { children }
            | Node::Region { children, .. } => children,
            Node::Other => &[],
        }
    }
}
