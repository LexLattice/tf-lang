import { effectOf } from '../../tf-l0-check/src/effect-lattice.mjs';

export function emitParWriteSafety(ir, opts = {}) {
  const catalog = normalizeCatalog(opts.catalog);
  const hasConflict = detectParallelSameUriWrite(ir, catalog);
  const lines = [];
  lines.push('(declare-sort URI 0)');
  lines.push('(declare-fun InParSameURI () Bool)');
  if (hasConflict) {
    lines.push('(assert InParSameURI)');
  }
  lines.push('(assert (not InParSameURI))');
  lines.push('(check-sat)');
  return lines.join('\n') + '\n';
}

export function emitCommutationEquiv(irSeqEP, irSeqPE, opts = {}) {
  const catalog = normalizeCatalog(opts.catalog);
  const outA = encodeSequence(irSeqEP, catalog, 'input');
  const outB = encodeSequence(irSeqPE, catalog, 'input');
  const lines = [];
  lines.push('(declare-sort Val 0)');
  lines.push('(declare-fun E (Val) Val)');
  lines.push('(declare-fun P (Val) Val)');
  lines.push('(declare-const input Val)');
  lines.push('(assert (forall ((x Val)) (= (E (P x)) (P (E x)))))');
  lines.push(`(define-const outA Val ${outA})`);
  lines.push(`(define-const outB Val ${outB})`);
  lines.push('(assert (not (= outA outB)))');
  lines.push('(check-sat)');
  return lines.join('\n') + '\n';
}

function detectParallelSameUriWrite(node, catalog) {
  let found = false;
  walk(node, (current) => {
    if (found || !current || typeof current !== 'object') {
      return;
    }
    if (current.node === 'Par' && Array.isArray(current.children)) {
      const branchUris = current.children.map((child) => collectWriteUris(child, catalog));
      for (let i = 0; i < branchUris.length; i++) {
        const left = branchUris[i];
        if (left.length === 0) {
          continue;
        }
        for (let j = i + 1; j < branchUris.length; j++) {
          const right = branchUris[j];
          if (right.length === 0) {
            continue;
          }
          if (hasIntersection(left, right)) {
            found = true;
            return;
          }
        }
      }
    }
  });
  return found;
}

function collectWriteUris(node, catalog) {
  if (!node || typeof node !== 'object') {
    return [];
  }
  if (node.node === 'Prim') {
    const primId = typeof node.prim === 'string' ? node.prim : null;
    if (!primId) {
      return [];
    }
    const family = effectOf(primId, catalog);
    if (family !== 'Storage.Write') {
      return [];
    }
    const uri = extractUri(node.args);
    return uri ? [uri] : [];
  }
  if (!Array.isArray(node.children)) {
    return [];
  }
  const uris = [];
  for (const child of node.children) {
    uris.push(...collectWriteUris(child, catalog));
  }
  return uniqueStrings(uris);
}

function encodeSequence(ir, catalog, seed) {
  const prims = collectSequentialPrims(ir);
  if (prims.length !== 2) {
    throw new Error('Expected two-step sequence');
  }
  const ops = prims.map((prim) => mapPrimToOp(prim, catalog));
  if (!containsBothOps(ops)) {
    throw new Error('Expected sequence containing Observability and Pure effects');
  }
  return ops.reduce((acc, op) => `(${op} ${acc})`, seed);
}

function collectSequentialPrims(node) {
  if (!node || typeof node !== 'object') {
    return [];
  }
  if (node.node === 'Prim') {
    return [node];
  }
  if (node.node === 'Par') {
    throw new Error('Parallel nodes are not supported in commutation proofs');
  }
  const collected = [];
  if (Array.isArray(node.children)) {
    for (const child of node.children) {
      collected.push(...collectSequentialPrims(child));
    }
  }
  return collected;
}

function mapPrimToOp(prim, catalog) {
  const primId = typeof prim.prim === 'string' ? prim.prim : null;
  if (!primId) {
    throw new Error('Invalid primitive node');
  }
  const family = effectOf(primId, catalog);
  if (family === 'Observability') {
    return 'E';
  }
  if (family === 'Pure') {
    return 'P';
  }
  throw new Error(`Unsupported effect family: ${family}`);
}

function containsBothOps(ops) {
  const unique = new Set(ops);
  return unique.has('E') && unique.has('P');
}

function extractUri(args) {
  if (!args || typeof args !== 'object') {
    return null;
  }
  const uri = args.uri;
  if (typeof uri === 'string' && uri.length > 0) {
    return uri;
  }
  return null;
}

function uniqueStrings(values) {
  const result = [];
  const seen = new Set();
  for (const value of values) {
    if (typeof value !== 'string' || value.length === 0) {
      continue;
    }
    if (seen.has(value)) {
      continue;
    }
    seen.add(value);
    result.push(value);
  }
  return result;
}

function hasIntersection(a, b) {
  const lookup = new Set(a);
  for (const value of b) {
    if (lookup.has(value)) {
      return true;
    }
  }
  return false;
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

function normalizeCatalog(raw) {
  if (raw && typeof raw === 'object') {
    return raw;
  }
  return { primitives: [] };
}
