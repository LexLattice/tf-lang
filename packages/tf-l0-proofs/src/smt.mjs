export function emitSMT(ir) {
  const declarations = [];
  const conflictAssertions = [];
  const conflictNames = [];
  let parIndex = 0;

  walk(ir, (node) => {
    if (!node || typeof node !== 'object') {
      return;
    }
    if (node.node === 'Par' && Array.isArray(node.children)) {
      const currentPar = parIndex++;
      const childUris = node.children.map((child) => selectUri(child));
      for (let i = 0; i < childUris.length; i++) {
        for (let j = i + 1; j < childUris.length; j++) {
          const conflictName = `conflict_p${currentPar}_${i}_${j}`;
          declarations.push(`(declare-const ${conflictName} Bool)`);
          const left = stringLiteral(childUris[i]);
          const right = stringLiteral(childUris[j]);
          conflictAssertions.push(
            `(assert (= ${conflictName} (= ${left} ${right})))`
          );
          conflictNames.push(conflictName);
        }
      }
    }
  });

  const body = [];
  if (declarations.length === 0 && conflictAssertions.length === 0) {
    // still provide a deterministic empty model
  } else {
    body.push(...declarations);
    body.push(...conflictAssertions);
  }

  const orArgs = conflictNames.join(' ');
  body.push(`(assert (not (or${orArgs ? ' ' + orArgs : ''})))`);
  body.push('(check-sat)');
  return body.join('\n') + '\n';
}

function walk(node, visit) {
  if (!node || typeof node !== 'object') {
    return;
  }
  visit(node);
  if (Array.isArray(node.children)) {
    for (const child of node.children) {
      walk(child, visit);
    }
  }
}

function selectUri(node) {
  const uris = collectWriteUris(node);
  if (uris.length > 0) {
    return uris[0];
  }
  const fromArgs = extractUriFromArgs(node?.args || {});
  if (fromArgs) {
    return fromArgs;
  }
  return 'res://unknown';
}

function collectWriteUris(node) {
  if (!node || typeof node !== 'object') {
    return [];
  }
  const uris = [];
  if (Array.isArray(node.writes)) {
    for (const w of node.writes) {
      const uri = w?.uri;
      if (typeof uri === 'string' && uri.length > 0) {
        uris.push(uri);
      }
    }
  }
  if (uris.length === 0 && Array.isArray(node.children)) {
    for (const child of node.children) {
      uris.push(...collectWriteUris(child));
    }
  }
  if (uris.length === 0 && node.node === 'Prim') {
    const inferred = extractUriFromArgs(node.args || {});
    if (inferred) {
      uris.push(inferred);
    }
  }
  return uris;
}

function extractUriFromArgs(args = {}) {
  if (!args || typeof args !== 'object') {
    return null;
  }
  const keys = ['uri', 'resource_uri', 'bucket_uri'];
  for (const key of keys) {
    const val = args[key];
    if (typeof val === 'string' && val.length > 0) {
      return val;
    }
  }
  return null;
}

function stringLiteral(value) {
  const s = typeof value === 'string' ? value : 'res://unknown';
  const escaped = s.replace(/\\/g, '\\\\').replace(/"/g, '\\"');
  return `"${escaped}"`;
}
