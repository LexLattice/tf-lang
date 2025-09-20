const UNKNOWN_URI = 'res://unknown';

function isObject(value) {
  return value !== null && typeof value === 'object';
}

function stringLiteral(value) {
  return JSON.stringify(String(value ?? UNKNOWN_URI));
}

function isConcreteUri(uri) {
  return typeof uri === 'string' && uri.length > 0 && !/[<>]/.test(uri);
}

function argUri(node) {
  if (!isObject(node?.args)) {
    return null;
  }
  const candidate = node.args.uri || node.args.resource_uri;
  return typeof candidate === 'string' && candidate.length > 0 ? candidate : null;
}

function gatherUris(node) {
  if (!isObject(node)) {
    return [];
  }

  let sawWrites = false;
  const concrete = new Set();
  const placeholders = new Set();

  if (Array.isArray(node.writes) && node.writes.length > 0) {
    sawWrites = true;
    for (const write of node.writes) {
      const uri = write && typeof write.uri === 'string' ? write.uri : null;
      if (!uri) {
        continue;
      }
      if (isConcreteUri(uri)) {
        concrete.add(uri);
      } else {
        placeholders.add(uri);
      }
    }
  }

  if (concrete.size > 0) {
    return Array.from(concrete);
  }

  const fromArgs = argUri(node);
  if (fromArgs) {
    return [fromArgs];
  }

  if (Array.isArray(node.children)) {
    const viaChildren = new Set();
    for (const child of node.children) {
      for (const uri of gatherUris(child)) {
        viaChildren.add(uri);
      }
    }
    if (viaChildren.size > 0) {
      return Array.from(viaChildren);
    }
  }

  if (sawWrites && placeholders.size > 0) {
    return Array.from(placeholders);
  }

  return [];
}

function uriSymbol(node) {
  const uris = gatherUris(node);
  if (uris.length === 1) {
    return stringLiteral(uris[0]);
  }
  return stringLiteral(UNKNOWN_URI);
}

export function emitSMT(ir) {
  const declarations = [];
  const pairAssertions = [];
  const conflictNames = [];
  let parIndex = 0;

  function visit(node) {
    if (!isObject(node)) {
      return;
    }

    if (node.node === 'Par' && Array.isArray(node.children)) {
      const localIndex = parIndex++;
      const childUris = node.children.map(uriSymbol);
      for (let i = 0; i < childUris.length; i++) {
        for (let j = i + 1; j < childUris.length; j++) {
          const name = `conflict_${localIndex}_${i}_${j}`;
          declarations.push(`(declare-const ${name} Bool)`);
          pairAssertions.push(`(assert (= ${name} (= ${childUris[i]} ${childUris[j]})))`);
          conflictNames.push(name);
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
  lines.push(...declarations);
  lines.push(...pairAssertions);
  if (conflictNames.length > 0) {
    lines.push(`(assert (not (or ${conflictNames.join(' ')})))`);
  } else {
    lines.push('(assert true)');
  }
  lines.push('(check-sat)');
  return lines.join('\n') + '\n';
}
