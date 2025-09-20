const INDENT = '  ';

export function formatDSL(ir) {
  const lines = formatNodeLines(ir, 0);
  return lines.join('\n');
}

export function renderIRTree(ir) {
  const out = [];
  walk(ir, 0, out);
  return out.join('\n');
}

function formatNodeLines(node, depth) {
  switch (node.node) {
    case 'Prim':
      return [formatPrim(node, depth)];
    case 'Seq':
      return formatBlock('seq', node.children, depth);
    case 'Par':
      return formatBlock('par', node.children, depth);
    case 'Region':
      return formatRegion(node, depth);
    default:
      throw new Error(`Unknown node type: ${node.node}`);
  }
}

function formatPrim(node, depth) {
  const base = indent(depth) + node.prim;
  const keys = Object.keys(node.args || {});
  if (!keys.length) return base;
  const sorted = keys.slice().sort();
  const args = sorted.map((key) => `${key}=${formatValue(node.args[key])}`).join(', ');
  return `${base}(${args})`;
}

function formatBlock(keyword, children, depth) {
  const lines = [`${indent(depth)}${keyword}{`];
  children.forEach((child, idx) => {
    const childLines = formatNodeLines(child, depth + 1);
    if (idx < children.length - 1) {
      const last = childLines.length - 1;
      childLines[last] = `${childLines[last]};`;
    }
    lines.push(...childLines);
  });
  lines.push(`${indent(depth)}}`);
  return lines;
}

function formatRegion(node, depth) {
  const keyword = regionKeyword(node.kind);
  const attrKeys = Object.keys(node.attrs || {});
  let header = `${indent(depth)}${keyword}`;
  if (attrKeys.length) {
    const sorted = attrKeys.slice().sort();
    const attrs = sorted.map((key) => `${key}=${formatValue(node.attrs[key])}`).join(', ');
    header += `(${attrs})`;
  }
  header += '{';
  const lines = [header];
  node.children.forEach((child, idx) => {
    const childLines = formatNodeLines(child, depth + 1);
    if (idx < node.children.length - 1) {
      const last = childLines.length - 1;
      childLines[last] = `${childLines[last]};`;
    }
    lines.push(...childLines);
  });
  lines.push(`${indent(depth)}}`);
  return lines;
}

function formatValue(value) {
  if (value === null) return 'null';
  if (Array.isArray(value)) {
    const items = value.map((item) => formatValue(item)).join(', ');
    return `[${items}]`;
  }
  if (typeof value === 'object') {
    const keys = Object.keys(value).sort();
    const inner = keys.map((key) => `${key}:${formatValue(value[key])}`).join(', ');
    return `{${inner}}`;
  }
  if (typeof value === 'string') {
    return `"${escapeString(value)}"`;
  }
  if (typeof value === 'number') {
    return Number.isFinite(value) ? String(value) : 'null';
  }
  if (typeof value === 'boolean') {
    return value ? 'true' : 'false';
  }
  return String(value);
}

function escapeString(value) {
  return value.replace(/\\/g, '\\\\').replace(/"/g, '\\"');
}

function indent(depth) {
  return INDENT.repeat(depth);
}

function regionKeyword(kind) {
  switch (kind) {
    case 'Authorize':
      return 'authorize';
    case 'Transaction':
      return 'txn';
    default:
      return kind.toLowerCase();
  }
}

function walk(node, depth, out) {
  const pad = indent(depth);
  switch (node.node) {
    case 'Prim': {
      const argsText = formatArgsObject(node.args);
      const suffix = argsText ? ` ${argsText}` : '';
      out.push(`${pad}Prim: ${node.prim}${suffix}`);
      break;
    }
    case 'Seq':
    case 'Par': {
      out.push(`${pad}${node.node}`);
      node.children.forEach((child) => walk(child, depth + 1, out));
      break;
    }
    case 'Region': {
      const attrs = formatRegionAttrs(node.attrs);
      const suffix = attrs ? ` ${attrs}` : '';
      out.push(`${pad}${node.kind}${suffix}`);
      node.children.forEach((child) => walk(child, depth + 1, out));
      break;
    }
    default:
      throw new Error(`Unknown node type: ${node.node}`);
  }
}

function formatArgsObject(args = {}) {
  const keys = Object.keys(args);
  if (!keys.length) return '';
  const sorted = keys.slice().sort();
  const inner = sorted.map((key) => `${key}:${formatValue(args[key])}`).join(', ');
  return `{${inner}}`;
}

function formatRegionAttrs(attrs = {}) {
  const keys = Object.keys(attrs);
  if (!keys.length) return '';
  const sorted = keys.slice().sort();
  const parts = sorted.map((key) => `${key}=${formatValue(attrs[key])}`);
  return `(${parts.join(', ')})`;
}
