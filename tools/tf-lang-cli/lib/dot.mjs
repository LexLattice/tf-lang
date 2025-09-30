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
    if (typeof out.var === "string") outputs.add(out.var);
    if (Array.isArray(out.vars)) {
      for (const v of out.vars) if (typeof v === "string") outputs.add(v);
    }
  }
  return outputs;
}

function collectDependencies(node) {
  const refs = new Set();

  function visit(value, key = "") {
    if (key === "out" || value === null || value === undefined) return;
    if (typeof value === "string") {
      const found = extractVar(value);
      if (found) refs.add(found);
      return;
    }
    if (Array.isArray(value)) { for (const item of value) visit(item); return; }
    if (typeof value === "object") {
      if (typeof value.var === "string") refs.add(value.var);
      for (const [childKey, childValue] of Object.entries(value)) visit(childValue, childKey);
    }
  }

  for (const [key, val] of Object.entries(node ?? {})) visit(val, key);
  return refs;
}

/** Format a human label for the node, including when guard if present. */
function nodeLabel(node) {
  const parts = [node.id];
  const kind = node.kind ? String(node.kind) : "";
  const op = node?.spec?.op ? `:${node.spec.op}` : "";
  if (kind) parts.push(kind + op);
  const when = node?.when;
  if (when !== undefined && when !== null) {
    let whenText;
    if (typeof when === "string") {
      whenText = when;
    } else if (typeof when === "object") {
      if (when.op === "not" && typeof when.var === "string") whenText = `¬${when.var}`;
      else if (typeof when.var === "string") whenText = when.var.startsWith("@") ? when.var : `@${when.var}`;
      else whenText = JSON.stringify(when);
    } else {
      whenText = String(when);
    }
    parts.push(`when: ${whenText}`);
  }
  return parts.join("\n");
}

/** Optionally add dashed edges from guard variable producers to guarded nodes. */
function collectWhenGuardDeps(node) {
  const guards = new Set();
  const when = node?.when;
  if (when == null) return guards;
  if (typeof when === "string") {
    const v = extractVar(when);
    if (v) guards.add(v);
  } else if (typeof when === "object") {
    if (typeof when.var === "string") guards.add(when.var.replace(/^@/, ""));
    else if (when.op === "not" && typeof when.var === "string") guards.add(when.var.replace(/^@/, ""));
  }
  return guards;
}

function buildDotFromNodes(nodes = [], { title = "pipeline", strict = true } = {}) {
  const lines = [];
  lines.push(`digraph ${quote(title)} {`);
  lines.push("  rankdir=LR;");
  lines.push("  node [shape=box, style=rounded];");

  const varToNode = new Map();

  // Declare nodes and collect producers
  nodes.forEach((node) => {
    if (!node || typeof node !== "object" || !node.id) return;
    const label = nodeLabel(node);
    lines.push(`  ${quote(node.id)} [label=${quote(label)}];`);

    for (const output of collectOutputs(node)) {
      if (varToNode.has(output)) {
        const existing = varToNode.get(output);
        throw new Error(
          `Output variable "${output}" defined by multiple nodes: "${existing}" and "${node.id}"`
        );
      }
      varToNode.set(output, node.id);
    }
  });

  const edges = new Set();
  const externals = new Set();

  // Data-flow edges
  nodes.forEach((node) => {
    if (!node || typeof node !== "object" || !node.id) return;
    const nodeId = node.id;

    for (const dep of collectDependencies(node)) {
      const src = varToNode.get(dep);
      if (src) {
        edges.add(`  ${quote(src)} -> ${quote(nodeId)};`);
      } else {
        externals.add(dep);
        edges.add(`  ${quote(`@${dep}`)} -> ${quote(nodeId)};`);
      }
    }

    // Guard edges (dashed)
    for (const g of collectWhenGuardDeps(node)) {
      const src = varToNode.get(g);
      if (src && src !== nodeId) {
        edges.add(`  ${quote(src)} -> ${quote(nodeId)} [style=dashed];`);
      }
    }
  });

  if (externals.size > 0 && strict) {
    const sorted = [...externals].sort();
    const formatted = sorted.map((name) => `"${name}"`).join(", ");
    throw new Error(
      `Unresolved input variable(s): ${formatted}. Ensure each variable is produced before use or rerun with --strict-graph=false to allow externals.`
    );
  }

  if (externals.size > 0) {
    lines.push("  node [shape=ellipse, style=dashed];");
    for (const ext of externals) lines.push(`  ${quote(`@${ext}`)};`);
    lines.push("  node [shape=box, style=rounded];");
  }

  for (const e of edges) lines.push(e);
  lines.push("}");
  return lines.join("\n");
}

/**
 * Build DOT for a pipeline (doc.nodes) or a monitor bundle (doc.monitors with nodes per monitor).
 * - strict: if true, unresolved inputs fail; if false, render externals as dashed ellipses.
 */
export function buildDotGraph(doc = {}, options = {}) {
  const { strict = true } = options ?? {};
  if (Array.isArray(doc?.nodes)) {
    return buildDotFromNodes(doc.nodes, { title: doc.pipeline_id || doc.pipeline || "pipeline", strict });
  }
  if (Array.isArray(doc?.monitors)) {
    const lines = [];
    const title = doc.bundle_id || "monitors";
    lines.push(`digraph ${quote(title)} {`);
    lines.push("  rankdir=LR;");

    doc.monitors.forEach((mon, i) => {
      const cluster = `cluster_${i}`;
      const label = mon.monitor_id || `monitor_${i}`;
      lines.push(`  subgraph ${cluster} {`);
      lines.push(`    label=${quote(label)};`);
      const sub = buildDotFromNodes(mon.nodes || [], { title: label, strict });
      // Extract lines between braces
      const inner = sub.split("\n").slice(2, -1).map((l) => "    " + l);
      lines.push(...inner);
      lines.push("  }");
    });

    lines.push("}");
    return lines.join("\n");
  }

  // Fallback
  return buildDotFromNodes([], { title: "pipeline", strict });
}
