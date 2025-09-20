const INDENT = '  ';
const IDENT_KEY_RE = /^[A-Za-z_][A-Za-z0-9_.-]*$/;

export function formatDSL(ir) {
  const lines = formatNode(ir, 0);
  return lines.join('\n');
}

export function renderIRTree(ir) {
  return renderTreeLines(ir, 0).join('\n');
}

function formatNode(node, level) {
  if (!node || typeof node !== 'object') {
    return [`${indent(level)}${String(node)}`];
  }

  if (node.node === 'Prim') {
    return [`${indent(level)}${formatPrim(node)}`];
  }

  if (node.node === 'Seq' && node.syntax === 'block') {
    return formatBlock('seq', node.children ?? [], level);
  }

  if (node.node === 'Par') {
    return formatBlock('par', node.children ?? [], level);
  }

  if (node.node === 'Region') {
    return formatRegion(node, level);
  }

  if (node.node === 'Seq') {
    return formatPipeline(node, level);
  }

  if (Array.isArray(node)) {
    return [`${indent(level)}${formatLiteral(node)}`];
  }

  return [`${indent(level)}${String(node)}`];
}

function formatPrim(node) {
  const name = typeof node.prim === 'string' ? node.prim : '';
  const args = node.args && typeof node.args === 'object' ? node.args : {};
  const keys = Object.keys(args);
  if (keys.length === 0) return name;
  const parts = keys.sort().map((key) => `${key}=${formatLiteral(args[key])}`);
  return `${name}(${parts.join(', ')})`;
}

function formatBlock(name, children, level) {
  const lines = [`${indent(level)}${name}{`];
  const count = children.length;
  children.forEach((child, index) => {
    const childLines = formatNode(child, level + 1);
    if (index < count - 1) {
      childLines[childLines.length - 1] = `${childLines[childLines.length - 1]};`;
    }
    lines.push(...childLines);
  });
  lines.push(`${indent(level)}}`);
  return lines;
}

function formatRegion(node, level) {
  const name = typeof node.kind === 'string' ? node.kind.toLowerCase() : 'region';
  const attrs = node.attrs && typeof node.attrs === 'object' ? node.attrs : {};
  const keys = Object.keys(attrs).sort();
  const attrParts = keys.map((key) => `${key}=${formatLiteral(attrs[key])}`);
  const header = attrParts.length > 0
    ? `${indent(level)}${name}(${attrParts.join(', ')}){`
    : `${indent(level)}${name}{`;
  const lines = [header];
  const children = node.children ?? [];
  children.forEach((child, index) => {
    const childLines = formatNode(child, level + 1);
    if (index < children.length - 1) {
      childLines[childLines.length - 1] = `${childLines[childLines.length - 1]};`;
    }
    lines.push(...childLines);
  });
  lines.push(`${indent(level)}}`);
  return lines;
}

function formatPipeline(node, level) {
  const children = node.children ?? [];
  if (children.length === 0) {
    return [`${indent(level)}`];
  }
  const parts = children.map((child) => renderInline(child));
  const joined = parts.join(' |> ');
  return indentMultiline(joined, level);
}

function renderInline(node) {
  if (!node || typeof node !== 'object') {
    return String(node);
  }
  if (node.node === 'Prim') {
    return formatPrim(node);
  }
  return formatNode(node, 0).join('\n');
}

function indentMultiline(text, level) {
  const pad = indent(level);
  return text.split('\n').map((line) => `${pad}${line}`);
}

function indent(level) {
  return INDENT.repeat(level);
}

function renderTreeLines(node, level) {
  if (!node || typeof node !== 'object') {
    return [`${indent(level)}${String(node)}`];
  }

  if (node.node === 'Prim') {
    const args = formatArgsForShow(node.args);
    const suffix = args ? ` ${args}` : '';
    return [`${indent(level)}Prim: ${node.prim}${suffix}`];
  }

  if (node.node === 'Seq') {
    const lines = [`${indent(level)}Seq`];
    for (const child of node.children ?? []) {
      lines.push(...renderTreeLines(child, level + 1));
    }
    return lines;
  }

  if (node.node === 'Par') {
    const lines = [`${indent(level)}Par`];
    for (const child of node.children ?? []) {
      lines.push(...renderTreeLines(child, level + 1));
    }
    return lines;
  }

  if (node.node === 'Region') {
    const attrs = formatArgsForShow(node.attrs);
    const suffix = attrs ? ` ${attrs}` : '';
    const lines = [`${indent(level)}Region: ${node.kind}${suffix}`];
    for (const child of node.children ?? []) {
      lines.push(...renderTreeLines(child, level + 1));
    }
    return lines;
  }

  return [`${indent(level)}${String(node.node ?? node)}`];
}

function formatArgsForShow(obj) {
  if (!obj || typeof obj !== 'object' || Array.isArray(obj)) return '';
  const keys = Object.keys(obj);
  if (keys.length === 0) return '';
  const parts = keys.sort().map((key) => `${key}:${formatLiteral(obj[key])}`);
  return `{${parts.join(', ')}}`;
}

function formatLiteral(value) {
  if (value === null) return 'null';
  if (typeof value === 'number') {
    return Number.isFinite(value) ? String(value) : 'null';
  }
  if (typeof value === 'boolean') {
    return value ? 'true' : 'false';
  }
  if (typeof value === 'string') {
    return `"${escapeString(value)}"`;
  }
  if (Array.isArray(value)) {
    return `[${value.map((item) => formatLiteral(item)).join(', ')}]`;
  }
  if (value && typeof value === 'object') {
    const keys = Object.keys(value).sort();
    const parts = keys.map((key) => {
      const keyText = IDENT_KEY_RE.test(key) ? key : formatLiteral(String(key));
      return `${keyText}:${formatLiteral(value[key])}`;
    });
    return `{${parts.join(', ')}}`;
  }
  return `"${escapeString(String(value))}"`;
}

function escapeString(value) {
  return value
    .replace(/\\/g, '\\\\')
    .replace(/"/g, '\\"')
    .replace(/\n/g, '\\n')
    .replace(/\r/g, '\\r')
    .replace(/\t/g, '\\t');
}
