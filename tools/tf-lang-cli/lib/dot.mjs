function quote(value) {
  const text = String(value ?? "");
  return `"${text.replace(/\\/g, "\\\\").replace(/"/g, '\\"')}"`;
}

function extractVar(ref) {
  if (typeof ref !== "string") return null;
  if (!ref.startsWith("@")) return null;
  const body = ref.slice(1);
  const match = body.match(/^[A-Za-z0-9_]+/);
  return match ? match[0] : null;
}

function collectOutputs(node) {
  const outputs = new Set();
  const out = node?.out;
  if (typeof out === "string") {
    outputs.add(out);
  } else if (out && typeof out === "object") {
    if (typeof out.var === "string") {
      outputs.add(out.var);
    }
    if (Array.isArray(out.vars)) {
      for (const v of out.vars) {
        if (typeof v === "string") {
          outputs.add(v);
        }
      }
    }
  }
  return outputs;
}

function collectDependencies(node) {
  const refs = new Set();

  function visit(value, key = "") {
    if (key === "out" || value === null || value === undefined) {
      return;
    }
    if (typeof value === "string") {
      const found = extractVar(value);
      if (found) {
        refs.add(found);
      }
      return;
    }
    if (Array.isArray(value)) {
      for (const item of value) {
        visit(item);
      }
      return;
    }
    if (typeof value === "object") {
      if (typeof value.var === "string") {
        refs.add(value.var);
      }
      for (const [childKey, childValue] of Object.entries(value)) {
        visit(childValue, childKey);
      }
    }
  }

  for (const [key, val] of Object.entries(node ?? {})) {
    visit(val, key);
  }

  return refs;
}

export function buildDotGraph(doc = {}, options = {}) {
  const { strict = true } = options ?? {};
  const nodes = Array.isArray(doc?.nodes) ? doc.nodes : [];
  const pipelineId = doc?.pipeline_id || doc?.pipeline || "pipeline";
  const lines = [];
  lines.push(`digraph ${quote(pipelineId)} {`);
  lines.push("  rankdir=LR;");
  lines.push("  node [shape=box, style=rounded];");

  const varToNode = new Map();

  for (const node of nodes) {
    if (!node || typeof node !== "object") continue;
    const nodeId = node.id ? String(node.id) : null;
    if (!nodeId) continue;
    const kind = node.kind ? String(node.kind) : "";
    const label = kind ? `${nodeId} (${kind})` : nodeId;
    lines.push(`  ${quote(nodeId)} [label=${quote(label)}];`);
    for (const output of collectOutputs(node)) {
      if (varToNode.has(output)) {
        const existing = varToNode.get(output);
        throw new Error(
          `Output variable "${output}" defined by multiple nodes: "${existing}" and "${nodeId}"`,
        );
      }
      varToNode.set(output, nodeId);
    }
  }

  const edges = new Set();
  const externals = new Set();

  for (const node of nodes) {
    if (!node || typeof node !== "object" || !node.id) continue;
    const nodeId = String(node.id);
    for (const dep of collectDependencies(node)) {
      const src = varToNode.get(dep);
      if (src) {
        edges.add(`  ${quote(src)} -> ${quote(nodeId)};`);
      } else {
        externals.add(dep);
        edges.add(`  ${quote(`@${dep}`)} -> ${quote(nodeId)};`);
      }
    }
  }

  if (externals.size > 0 && strict) {
    const sorted = [...externals].sort();
    const formatted = sorted.map((name) => `"${name}"`).join(", ");
    throw new Error(
      `Unresolved input variable(s): ${formatted}. Ensure each variable is produced before use or rerun with --strict-graph=false to allow externals.`,
    );
  }

  if (externals.size > 0) {
    lines.push("  node [shape=ellipse, style=dashed];");
    for (const ext of externals) {
      lines.push(`  ${quote(`@${ext}`)};`);
    }
    lines.push("  node [shape=box, style=rounded];");
  }

  for (const edge of edges) {
    lines.push(edge);
  }

  lines.push("}");
  return lines.join("\n");
}
