function graphLabel(value) {
  return String(value).replace(/"/g, '\\"');
}

function formatWhenClause(when) {
  if (when == null) return null;
  if (typeof when === 'string') return when;
  if (typeof when === 'object') {
    if (when.op === 'not' && typeof when.var === 'string') return `¬${when.var}`;
    if (typeof when.var === 'string') {
      return when.var.startsWith('@') ? when.var : `@${when.var}`;
    }
  }
  return JSON.stringify(when);
}

function extractWhenVars(when) {
  if (when == null) return [];
  if (typeof when === 'string') {
    const match = when.match(/^@([A-Za-z0-9_]+)/);
    return match ? [match[1]] : [];
  }
  if (typeof when === 'object') {
    if (typeof when.var === 'string') return [when.var.replace(/^@/, '')];
    if (when.op === 'not' && typeof when.var === 'string') return [when.var.replace(/^@/, '')];
  }
  return [];
}

function formatNodeLabel(node) {
  const parts = [node.id];
  switch (node.kind) {
    case 'Publish':
      parts.push(`Publish: ${node.channel ?? ''}`);
      break;
    case 'Subscribe':
      parts.push(`Subscribe: ${node.channel ?? ''}`);
      break;
    case 'Transform':
      parts.push(`Transform: ${node.spec?.op ?? ''}`);
      break;
    case 'Keypair':
      parts.push(`Keypair: ${node.algorithm ?? ''}`);
      break;
    default:
      parts.push(node.kind ?? '');
      break;
  }
  const whenText = formatWhenClause(node.when);
  if (whenText) parts.push(`when: ${whenText}`);
  return parts.filter(Boolean).join('\n');
}

function collectVarProducers(nodes) {
  const map = new Map();
  nodes.forEach((node, idx) => {
    const outVar = node.out?.var;
    if (typeof outVar === 'string') {
      map.set(outVar, idx);
    }
  });
  return map;
}

function collectRefs(value, acc) {
  if (value == null) return;
  if (typeof value === 'string') {
    if (value.startsWith('@')) {
      const match = value.slice(1).match(/^([A-Za-z0-9_]+)/);
      if (match) acc.add(match[1]);
    }
    return;
  }
  if (Array.isArray(value)) {
    value.forEach((item) => collectRefs(item, acc));
    return;
  }
  if (typeof value === 'object') {
    Object.values(value).forEach((item) => collectRefs(item, acc));
  }
}

function collectNodeRefs(node) {
  const refs = new Set();
  const skip = new Set(['id', 'kind', 'out', 'when', 'monitor_id', 'pipeline_id', 'description', 'created_at', 'effects']);
  for (const [key, value] of Object.entries(node)) {
    if (skip.has(key)) continue;
    collectRefs(value, refs);
  }
  return refs;
}

function buildGraphElements(nodes, { prefix, indent, showWhenEdges }) {
  const lines = [];
  const edges = [];
  const seen = new Set();
  const producers = collectVarProducers(nodes);

  nodes.forEach((node, idx) => {
    const nodeName = `${prefix}${idx}`;
    const label = graphLabel(formatNodeLabel(node));
    lines.push(`${indent}${nodeName} [label="${label}"];`);
    const refs = collectNodeRefs(node);
    refs.forEach((ref) => {
      const srcIdx = producers.get(ref);
      if (srcIdx == null || srcIdx === idx) return;
      const edge = `${indent}${prefix}${srcIdx} -> ${nodeName};`;
      if (!seen.has(edge)) {
        seen.add(edge);
        edges.push(edge);
      }
    });
    if (showWhenEdges) {
      const guardVars = extractWhenVars(node.when);
      guardVars.forEach((varName) => {
        const srcIdx = producers.get(varName);
        if (srcIdx == null || srcIdx === idx) return;
        const edge = `${indent}${prefix}${srcIdx} -> ${nodeName} [style=dashed];`;
        if (!seen.has(edge)) {
          seen.add(edge);
          edges.push(edge);
        }
      });
    }
  });

  return { nodeLines: lines, edgeLines: edges };
}

export function renderPipelineGraph(doc, options = {}) {
  const showWhenEdges = options.showWhenEdges !== false;
  const nodes = Array.isArray(doc.nodes) ? doc.nodes : [];
  const { nodeLines, edgeLines } = buildGraphElements(nodes, {
    prefix: 'n',
    indent: '  ',
    showWhenEdges,
  });
  return ['digraph G {', '  rankdir=LR;', ...nodeLines, ...edgeLines, '}'].join('\n');
}

export function renderMonitorGraph(doc, options = {}) {
  const showWhenEdges = options.showWhenEdges !== false;
  const monitors = Array.isArray(doc.monitors) ? doc.monitors : [];
  const lines = ['digraph G {', '  rankdir=LR;'];
  monitors.forEach((monitor, monitorIdx) => {
    const clusterName = `cluster_${monitorIdx}`;
    lines.push(`  subgraph ${clusterName} {`);
    lines.push(`    label="${graphLabel(monitor.monitor_id ?? `monitor_${monitorIdx}`)}";`);
    const { nodeLines, edgeLines } = buildGraphElements(monitor.nodes ?? [], {
      prefix: `m${monitorIdx}_n`,
      indent: '    ',
      showWhenEdges,
    });
    lines.push(...nodeLines);
    lines.push(...edgeLines);
    lines.push('  }');
  });
  lines.push('}');
  return lines.join('\n');
}
