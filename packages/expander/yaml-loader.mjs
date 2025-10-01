import YAML from 'yaml';

const { Parser, CST } = YAML;

function resolveScalar(token) {
  if (!token) return null;
  const resolved = CST.resolveAsScalar(
    token,
    false,
    (offset, code, message) => {
      throw new Error(`YAML scalar error [${code}] at offset ${offset}: ${message}`);
    },
  );
  if (resolved && typeof resolved === 'object' && 'value' in resolved) {
    let value = resolved.value;
    if (token.type === 'scalar' && typeof value === 'string') {
      const lowered = value.toLowerCase();
      if (lowered === 'null' || lowered === '~') {
        return null;
      }
      if (lowered === 'true') {
        return true;
      }
      if (lowered === 'false') {
        return false;
      }
      if (/^[+-]?(?:0|[1-9][0-9]*)$/.test(value)) {
        return Number(value);
      }
      if (/^[+-]?(?:0|[1-9][0-9]*)(?:\.[0-9]+)?(?:[eE][+-]?[0-9]+)?$/.test(value)) {
        return Number(value);
      }
    }
    return value;
  }
  return resolved;
}

function extractMacroInvocation(source, start) {
  let index = start;
  const length = source.length;
  let depth = 0;
  let inSingle = false;
  let inDouble = false;
  let sawParen = false;
  let end = start;

  const advance = () => {
    index += 1;
  };

  while (index < length) {
    const ch = source[index];
    if (inSingle) {
      if (ch === "'" && source[index - 1] !== '\\') {
        inSingle = false;
      }
      advance();
      continue;
    }
    if (inDouble) {
      if (ch === '"') {
        let escapes = 0;
        let back = index - 1;
        while (back >= start && source[back] === '\\') {
          escapes += 1;
          back -= 1;
        }
        if (escapes % 2 === 0) {
          inDouble = false;
        }
      }
      advance();
      continue;
    }

    if (ch === '#') {
      break;
    }
    if (ch === '"') {
      inDouble = true;
      advance();
      continue;
    }
    if (ch === "'") {
      inSingle = true;
      advance();
      continue;
    }
    if (ch === '(') {
      depth += 1;
      sawParen = true;
      advance();
      continue;
    }
    if (ch === ')') {
      if (depth === 0) {
        throw new Error('Unbalanced macro invocation in YAML');
      }
      depth -= 1;
      advance();
      if (depth === 0) {
        end = index;
        break;
      }
      continue;
    }
    if (!/\s/.test(ch)) {
      end = index + 1;
    }
    advance();
  }

  if (depth !== 0) {
    throw new Error('Unbalanced macro invocation in YAML');
  }
  if (!sawParen) {
    throw new Error('Expected macro invocation with parentheses');
  }

  let finalEnd = end;
  while (finalEnd > start && /[ \t]/.test(source[finalEnd - 1])) {
    finalEnd -= 1;
  }
  return source.slice(start, finalEnd);
}

function tryExtractMacro(node, context) {
  if (!node || node.type !== 'block-map') {
    return null;
  }
  if (!node.items || node.items.length === 0) {
    return null;
  }
  const first = node.items[0];
  if (!first || !first.key || typeof first.key.source !== 'string') {
    return null;
  }
  const keySource = first.key.source;
  if (!keySource.includes('(')) {
    return null;
  }
  const start = first.key.offset;
  if (typeof start !== 'number' || start < 0) {
    return null;
  }
  return extractMacroInvocation(context.source, start);
}

function convertFlowCollection(node, context) {
  const isMap = node.start.type === 'flow-map-start';
  if (isMap) {
    const out = {};
    for (const item of node.items) {
      if (!item) continue;
      const keyToken = item.key ?? null;
      const valueToken = item.value ?? null;
      const key = convertNode(keyToken, context);
      const value = convertNode(valueToken, context);
      if (key !== null && key !== undefined) {
        out[key] = value;
      }
    }
    return out;
  }
  if (node.start.type === 'flow-seq-start') {
    const out = [];
    for (const item of node.items) {
      if (!item) continue;
      const valueToken = item.value ?? item.key ?? null;
      out.push(convertNode(valueToken, context));
    }
    return out;
  }
  throw new Error(`Unsupported flow collection start: ${node.start.type}`);
}

function convertBlockSeq(node, context) {
  const out = [];
  for (const item of node.items) {
    if (!item) continue;
    out.push(convertNode(item.value ?? null, context));
  }
  return out;
}

function convertBlockMap(node, context) {
  const out = {};
  for (const item of node.items) {
    if (!item || !item.key) {
      continue;
    }
    const key = convertNode(item.key, context);
    if (key === null || key === undefined) {
      continue;
    }
    const macro = tryExtractMacro(item.value, context);
    if (macro !== null) {
      out[key] = macro;
      continue;
    }
    out[key] = convertNode(item.value ?? null, context);
  }
  return out;
}

function convertNode(node, context) {
  if (!node) {
    return null;
  }
  switch (node.type) {
    case 'block-map':
      return convertBlockMap(node, context);
    case 'block-seq':
      return convertBlockSeq(node, context);
    case 'flow-collection':
      return convertFlowCollection(node, context);
    case 'scalar':
    case 'double-quoted-scalar':
    case 'single-quoted-scalar':
    case 'block-scalar':
      return resolveScalar(node);
    default:
      throw new Error(`Unsupported YAML node type: ${node.type}`);
  }
}

export function loadYamlDocument(source) {
  const parser = new Parser();
  const tokens = Array.from(parser.parse(source));
  const doc = tokens.find((token) => token.type === 'document');
  if (!doc || !doc.value) {
    throw new Error('Expected a single YAML document');
  }
  return convertNode(doc.value, { source });
}

export default loadYamlDocument;
