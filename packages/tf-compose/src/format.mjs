const INDENT = '  ';
const IDENT_KEY_RE = /^[A-Za-z_][A-Za-z0-9_]*$/;

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

  if (node.node === 'Let') {
    return formatLet(node, level);
  }

  if (node.node === 'Include') {
    return formatInclude(node, level);
  }

  if (node.node === 'Ref') {
    return [`${indent(level)}${node.name}`];
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
  const parts = keys
    .sort((a, b) => a.localeCompare(b))
    .map((key) => `${key}=${formatLiteral(args[key])}`);
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

function formatLet(node, level) {
  const base = indent(level);
  const name = typeof node.name === 'string' ? node.name : '';
  const initLines = renderLetInit(node.init);

  const lines = [];
  if (initLines.length === 0) {
    lines.push(`${base}let ${name} = null`);
  } else {
    lines.push(`${base}let ${name} = ${initLines[0]}`);
    for (let i = 1; i < initLines.length; i += 1) {
      lines.push(`${base}${initLines[i]}`);
    }
  }

  if (node.body) {
    const bodyLines = formatNode(node.body, level + 1);
    lines.push(...bodyLines);
  }

  return lines;
}

function formatInclude(node, level) {
  const base = indent(level);
  const path = typeof node.path === 'string' ? node.path : '';
  return [`${base}include "${escapeString(path)}"`];
}

function renderLetInit(init) {
  if (init === undefined || init === null) return ['null'];
  if (typeof init === 'number' || typeof init === 'boolean') {
    return [String(init)];
  }
  if (typeof init === 'string') {
    return [`"${escapeString(init)}"`];
  }
  if (Array.isArray(init)) {
    return [formatLiteral(init)];
  }
  if (init && typeof init === 'object') {
    if (init.node) {
      return renderInline(init).split('\n');
    }
    return [formatLiteral(init)];
  }
  return ['null'];
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
  if (node.node === 'Ref') {
    return node.name || '';
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

  if (node.node === 'Ref') {
    return [`${indent(level)}Ref: ${node.name}`];
  }

  return [`${indent(level)}${String(node.node ?? node)}`];
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
    const keys = Object.keys(value).sort((a, b) => a.localeCompare(b));
    const parts = keys.map((key) => {
      const keyText = isIdent(key) ? key : JSON.stringify(key);
      return `${keyText}:${formatLiteral(value[key])}`;
    });
    return `{${parts.join(', ')}}`;
  }
  return `"${escapeString(String(value))}"`;
}

function isIdent(key) {
  return IDENT_KEY_RE.test(key);
}

function formatArgsForShow(obj) {
  if (!obj || typeof obj !== 'object' || Array.isArray(obj)) return '';
  const keys = Object.keys(obj).sort((a, b) => a.localeCompare(b));
  if (keys.length === 0) return '';
  const parts = keys.map((key) => {
    const keyText = isIdent(key) ? key : JSON.stringify(key);
    return `${keyText}:${formatLiteral(obj[key])}`;
  });
  return `{${parts.join(', ')}}`;
}

function escapeString(value) {
  return value
    .replace(/\\/g, '\\\\')
    .replace(/"/g, '\\"')
    .replace(/\n/g, '\\n')
    .replace(/\r/g, '\\r')
    .replace(/\t/g, '\\t');
}
