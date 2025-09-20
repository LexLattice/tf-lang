const UNKNOWN_URI = 'res://unknown';

function escapeString(value = '') {
  return value.replace(/\\/g, '\\\\').replace(/"/g, '\\"');
}

function isObject(value) {
  return value !== null && typeof value === 'object';
}

function firstWriteUri(node) {
  if (!isObject(node)) {
    return null;
  }

  if (Array.isArray(node.writes)) {
    for (const entry of node.writes) {
      const uri = entry?.uri;
      if (typeof uri === 'string' && uri.length > 0) {
        return uri;
      }
    }
  }

  const direct = node?.args?.uri || node?.args?.resource_uri;
  if (typeof direct === 'string' && direct.length > 0) {
    return direct;
  }

  if (Array.isArray(node.children)) {
    for (const child of node.children) {
      const uri = firstWriteUri(child);
      if (typeof uri === 'string' && uri.length > 0) {
        return uri;
      }
    }
  }

  return null;
}

export function emitSMT(ir) {
  const uriCache = new WeakMap();
  const uriDecls = [];
  const uriAssertions = [];
  const conflictDecls = [];
  const conflictAssertions = [];
  const conflictVars = [];

  let uriCounter = 0;
  let parCounter = 0;

  function ensureUri(node) {
    if (!isObject(node)) {
      const name = `uri_${uriCounter++}`;
      uriDecls.push(`(declare-const ${name} String)`);
      uriAssertions.push(`(assert (= ${name} \"${escapeString(UNKNOWN_URI)}\"))`);
      return { name, value: UNKNOWN_URI };
    }

    if (uriCache.has(node)) {
      return uriCache.get(node);
    }

    const name = `uri_${uriCounter++}`;
    const uri = firstWriteUri(node) || UNKNOWN_URI;
    uriDecls.push(`(declare-const ${name} String)`);
    uriAssertions.push(`(assert (= ${name} \"${escapeString(uri)}\"))`);
    const record = { name, value: uri };
    uriCache.set(node, record);
    return record;
  }

  function visit(node) {
    if (!isObject(node)) {
      return;
    }

    if (node.node === 'Par' && Array.isArray(node.children) && node.children.length > 0) {
      const currentPar = parCounter++;
      const childInfos = node.children.map(child => ensureUri(child));
      for (let i = 0; i < childInfos.length; i++) {
        for (let j = i + 1; j < childInfos.length; j++) {
          const infoA = childInfos[i];
          const infoB = childInfos[j];
          const varName = `conflict_${currentPar}_${i}_${j}`;
          conflictDecls.push(`(declare-const ${varName} Bool)`);
          conflictAssertions.push(
            `(assert (= ${varName} (= ${infoA.name} ${infoB.name})))`
          );
          conflictVars.push(varName);
        }
      }
    }

    if (Array.isArray(node.children)) {
      for (const child of node.children) {
        visit(child);
      }
    }
  }

  visit(ir);

  const lines = [];
  lines.push('; SMT encoding for parallel write conflicts');
  lines.push(...uriDecls);
  lines.push(...uriAssertions);
  lines.push(...conflictDecls);
  lines.push(...conflictAssertions);

  const finalAssert = conflictVars.length > 0
    ? `(assert (not (or ${conflictVars.join(' ')})))`
    : '(assert (not (or )))';
  lines.push(finalAssert);
  lines.push('(check-sat)');

  return lines.join('\n') + '\n';
}
