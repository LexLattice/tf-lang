const INDENT = '  ';

export function formatDSL(ir) {
  const lines = formatNode(ir, 0);
  return lines.join('\n');
}

export function formatTree(ir) {
  const lines = treeLines(ir, 0);
  return lines.join('\n');
}

function formatNode(node, depth) {
  if (!node) return [];
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
      if (node.prim) return [formatPrim(node, depth)];
      return [indent(depth) + String(node)];
  }
}

function formatPrim(node, depth) {
  const pad = indent(depth);
  const args = formatAssignments(node.args);
  if (!args) return pad + node.prim;
  return pad + node.prim + '(' + args + ')';
}

function formatBlock(keyword, children, depth) {
  const lines = [];
  lines.push(indent(depth) + keyword + '{');
  const childLines = formatChildren(children, depth + 1);
  lines.push(...childLines);
  lines.push(indent(depth) + '}');
  return lines;
}

function formatRegion(node, depth) {
  const keyword = regionKeyword(node.kind);
  const attrs = formatAssignments(node.attrs);
  const header = keyword + (attrs ? '(' + attrs + ')' : '');
  return formatBlock(header, node.children, depth);
}

function formatChildren(children = [], depth) {
  const lines = [];
  const list = children || [];
  for (let i = 0; i < list.length; i++) {
    const childLines = formatNode(list[i], depth);
    if (i < list.length - 1 && childLines.length > 0) {
      childLines[childLines.length - 1] += ';';
    }
    lines.push(...childLines);
  }
  return lines;
}

function formatAssignments(map = {}) {
  const keys = Object.keys(map);
  if (!keys.length) return '';
  keys.sort((a, b) => a.localeCompare(b));
  return keys.map(key => key + '=' + formatValue(map[key])).join(', ');
}

function formatValue(value) {
  if (value === null) return 'null';
  if (Array.isArray(value)) {
    return '[' + value.map(formatValue).join(', ') + ']';
  }
  if (typeof value === 'object') {
    return formatObject(value);
  }
  if (typeof value === 'string') return JSON.stringify(value);
  if (typeof value === 'boolean') return value ? 'true' : 'false';
  if (typeof value === 'number') return String(value);
  return JSON.stringify(value);
}

const IDENT_KEY = /^[A-Za-z_][A-Za-z0-9_\-.]*$/;

function formatObject(obj) {
  const keys = Object.keys(obj || {});
  if (!keys.length) return '{}';
  keys.sort((a, b) => a.localeCompare(b));
  const parts = keys.map(key => formatObjectKey(key) + ':' + formatValue(obj[key]));
  return '{' + parts.join(', ') + '}';
}

function formatObjectKey(key) {
  return IDENT_KEY.test(key) ? key : JSON.stringify(key);
}

function regionKeyword(kind) {
  if (kind === 'Authorize') return 'authorize';
  if (kind === 'Transaction') return 'txn';
  return (kind || 'region').toLowerCase();
}

function indent(depth) {
  return INDENT.repeat(depth);
}

function treeLines(node, depth) {
  if (!node) return [];
  switch (node.node) {
    case 'Prim': {
      const args = formatArgsObject(node.args);
      const label = indent(depth) + 'Prim: ' + node.prim + (args ? ' ' + args : '');
      return [label];
    }
    case 'Seq':
      return [indent(depth) + 'Seq', ...treeChildren(node.children, depth + 1)];
    case 'Par':
      return [indent(depth) + 'Par', ...treeChildren(node.children, depth + 1)];
    case 'Region': {
      const keyword = regionKeyword(node.kind);
      const attrs = formatAssignments(node.attrs);
      const label = indent(depth) + 'Region: ' + keyword + (attrs ? ' (' + attrs + ')' : '');
      return [label, ...treeChildren(node.children, depth + 1)];
    }
    default:
      return [indent(depth) + String(node)];
  }
}

function treeChildren(children = [], depth) {
  const lines = [];
  for (const child of children || []) {
    lines.push(...treeLines(child, depth));
  }
  return lines;
}

function formatArgsObject(args = {}) {
  const keys = Object.keys(args);
  if (!keys.length) return '';
  return formatObject(args);
}
