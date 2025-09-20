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
      for (let i = 0; i < node.children.length; i++) {
        const leftUris = collectWriteUris(node.children[i]);
        if (leftUris.length === 0) {
          continue;
        }
        for (let j = i + 1; j < node.children.length; j++) {
          const rightUris = collectWriteUris(node.children[j]);
          if (rightUris.length === 0) {
            continue;
          }
          for (let a = 0; a < leftUris.length; a++) {
            for (let b = 0; b < rightUris.length; b++) {
              const conflictName = `conflict_p${currentPar}_${i}_${j}_${a}_${b}`;
              declarations.push(`(declare-const ${conflictName} Bool)`);
              const left = stringLiteral(leftUris[a]);
              const right = stringLiteral(rightUris[b]);
              conflictAssertions.push(
                `(assert (= ${conflictName} (= ${left} ${right})))`
              );
              conflictNames.push(conflictName);
            }
          }
        }
      }
    }
  });

  const body = [];
  body.push(...declarations);
  body.push(...conflictAssertions);

  if (conflictNames.length === 0) {
    body.push('(assert true)');
  } else {
    body.push(`(assert (not (or ${conflictNames.join(' ')})))`);
  }
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

function collectWriteUris(node) {
  if (!node || typeof node !== 'object') {
    return [];
  }
  if (Array.isArray(node.writes) && node.writes.length > 0) {
    return dedupeAndSort(
      node.writes
        .map((entry) => concretizeUri(entry, node.args))
        .filter((uri) => typeof uri === 'string' && uri.length > 0)
    );
  }
  if (Array.isArray(node.children)) {
    const collected = [];
    for (const child of node.children) {
      collected.push(...collectWriteUris(child));
    }
    return dedupeAndSort(collected);
  }
  return [];
}

function stringLiteral(value) {
  const s = typeof value === 'string' ? value : 'res://unknown';
  const escaped = s.replace(/\\/g, '\\\\').replace(/"/g, '\\"');
  return `"${escaped}"`;
}

function concretizeUri(entry, args = {}) {
  const uri = normalizeUri(entry);
  if (uri && !isAbstractUri(uri)) {
    return uri;
  }
  const fromArgs = selectUriFromArgs(args);
  return fromArgs && fromArgs.length > 0 ? fromArgs : null;
}

function normalizeUri(entry) {
  if (typeof entry === 'string') {
    return entry;
  }
  if (entry && typeof entry === 'object' && typeof entry.uri === 'string') {
    return entry.uri;
  }
  return null;
}

function isAbstractUri(uri) {
  return uri === 'res://unknown' || /[<>]/.test(uri);
}

function selectUriFromArgs(args = {}) {
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

function dedupeAndSort(values = []) {
  return Array.from(new Set(values)).sort();
}
