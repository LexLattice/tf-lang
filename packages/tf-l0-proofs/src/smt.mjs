import { checkIR } from '../../tf-l0-check/src/check.mjs';

const EMPTY_CATALOG = { primitives: [] };

function quoteString(value) {
  const safe = String(value ?? 'res://unknown');
  return `"${safe.replace(/\\/g, '\\\\').replace(/"/g, '""')}"`;
}

function extractArgUri(node) {
  if (!node || typeof node !== 'object') {
    return null;
  }
  const args = node.args || {};
  if (typeof args.uri === 'string' && args.uri.length > 0) {
    return args.uri;
  }
  if (typeof args.resource_uri === 'string' && args.resource_uri.length > 0) {
    return args.resource_uri;
  }
  return null;
}

function gatherWriteUris(node) {
  try {
    const verdict = checkIR(node, EMPTY_CATALOG);
    const writes = Array.isArray(verdict?.writes) ? verdict.writes : [];
    const uris = writes
      .map(entry => (entry && typeof entry.uri === 'string') ? entry.uri : null)
      .filter((uri) => typeof uri === 'string' && uri.length > 0);
    if (uris.length > 0) {
      const uniq = Array.from(new Set(uris));
      if (uniq.length === 1) {
        return uniq[0];
      }
      uniq.sort();
      return uniq.join('|');
    }
  } catch {
    // ignore checker failures and fall back to args
  }
  const argUri = extractArgUri(node);
  return argUri || 'res://unknown';
}

export function emitSMT(ir) {
  const stringDecls = [];
  const stringAsserts = [];
  const boolDecls = [];
  const conflictAsserts = [];
  const conflictNames = [];

  let parCounter = 0;

  function processNode(node) {
    if (!node || typeof node !== 'object') {
      return;
    }

    if (node.node === 'Par') {
      const children = Array.isArray(node.children) ? node.children : [];
      const parId = parCounter++;
      if (children.length >= 2) {
        const uriNames = children.map((child, index) => {
          const uriName = `uri_${parId}_${index}`;
          const uriValue = gatherWriteUris(child);
          stringDecls.push(`(declare-const ${uriName} String)`);
          stringAsserts.push(`(assert (= ${uriName} ${quoteString(uriValue)}))`);
          return uriName;
        });

        for (let i = 0; i < children.length; i++) {
          for (let j = i + 1; j < children.length; j++) {
            const conflictName = `conflict_${parId}_${i}_${j}`;
            boolDecls.push(`(declare-const ${conflictName} Bool)`);
            conflictAsserts.push(`(assert (= ${conflictName} (= ${uriNames[i]} ${uriNames[j]})))`);
            conflictNames.push(conflictName);
          }
        }
      }
      for (const child of children) {
        processNode(child);
      }
      return;
    }

    if (Array.isArray(node.children)) {
      for (const child of node.children) {
        processNode(child);
      }
    }
  }

  processNode(ir);

  const lines = [];
  lines.push('; SMT encoding for parallel write conflicts');
  lines.push(...stringDecls);
  lines.push(...stringAsserts);
  lines.push(...boolDecls);
  lines.push(...conflictAsserts);

  if (conflictNames.length > 0) {
    lines.push(`(assert (not (or ${conflictNames.join(' ')})))`);
  } else {
    lines.push('(assert (not false))');
  }

  lines.push('(check-sat)');
  return lines.join('\n') + '\n';
}
