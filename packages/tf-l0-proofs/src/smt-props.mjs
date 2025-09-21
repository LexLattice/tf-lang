import { effectOf } from '../../tf-l0-check/src/effect-lattice.mjs';

export function emitParWriteSafety(ir, opts = {}) {
  const catalog = opts.catalog ?? {};
  const hasConflict = hasParallelSameUriWrites(ir, catalog);
  const lines = [];
  lines.push('(declare-sort URI 0)');
  lines.push('(declare-fun InParSameURI () Bool)');
  lines.push(hasConflict ? '(assert InParSameURI)' : '(assert (not InParSameURI))');
  lines.push('; Safety axiom: illegal to have same-URI writes in Par');
  lines.push('(assert (not InParSameURI))');
  lines.push('(check-sat)');
  return lines.join('\n') + '\n';
}

export function emitCommutationEquiv(irSeqEP, irSeqPE, opts = {}) {
  const catalog = opts.catalog ?? {};
  const stepsA = extractTwoStepSequence(irSeqEP, catalog);
  const stepsB = extractTwoStepSequence(irSeqPE, catalog);
  const lines = [];
  lines.push('(declare-sort Val 0)');
  lines.push('(declare-fun E (Val) Val)');
  lines.push('(declare-fun P (Val) Val)');
  lines.push('(assert (forall ((x Val)) (= (E (P x)) (P (E x)))))');
  lines.push('(declare-const x Val)');
  lines.push(`(define-fun outA () Val ${sequenceExpression(stepsA, 'x')})`);
  lines.push(`(define-fun outB () Val ${sequenceExpression(stepsB, 'x')})`);
  lines.push('(assert (not (= outA outB)))');
  lines.push('(check-sat)');
  return lines.join('\n') + '\n';
}

function hasParallelSameUriWrites(node, catalog) {
  return walkSome(node, (current) => {
    if (!current || typeof current !== 'object' || current.node !== 'Par') {
      return false;
    }
    const children = Array.isArray(current.children) ? current.children : [];
    const uriSets = children.map((child) => collectWriteUris(child, catalog));
    for (let i = 0; i < uriSets.length; i += 1) {
      for (let j = i + 1; j < uriSets.length; j += 1) {
        if (hasIntersection(uriSets[i], uriSets[j])) {
          return true;
        }
      }
    }
    return false;
  });
}

function collectWriteUris(node, catalog) {
  const uris = new Set();
  walk(node, (current) => {
    if (!current || typeof current !== 'object') {
      return;
    }
    if (current.node === 'Prim' && isStorageWrite(current.prim, catalog)) {
      const uri = normalizeUri(current?.args?.uri);
      if (uri) {
        uris.add(uri);
      }
    }
  });
  return uris;
}

function isStorageWrite(primName, catalog) {
  const family = effectOf(primName, catalog);
  return family === 'Storage.Write';
}

function normalizeUri(value) {
  if (typeof value !== 'string') {
    return null;
  }
  const trimmed = value.trim();
  return trimmed.length > 0 ? trimmed : null;
}

function hasIntersection(setA, setB) {
  if (!(setA instanceof Set) || !(setB instanceof Set)) {
    return false;
  }
  if (setA.size === 0 || setB.size === 0) {
    return false;
  }
  const [smaller, larger] = setA.size <= setB.size ? [setA, setB] : [setB, setA];
  for (const entry of smaller) {
    if (larger.has(entry)) {
      return true;
    }
  }
  return false;
}

function extractTwoStepSequence(ir, catalog) {
  const seq = findTwoStepSeq(ir);
  if (!seq) {
    throw new Error('Expected a Seq node with exactly two steps');
  }
  const children = Array.isArray(seq.children) ? seq.children : [];
  if (children.length !== 2) {
    throw new Error('Sequence must contain exactly two steps');
  }
  const families = children.map((child, index) => {
    if (!child || typeof child !== 'object' || child.node !== 'Prim') {
      throw new Error(`Sequence step ${index} must be a Prim node`);
    }
    const family = effectOf(child.prim, catalog);
    if (family !== 'Observability' && family !== 'Pure') {
      throw new Error(`Sequence step ${index} must have Observability or Pure effect`);
    }
    return family;
  });
  const uniqueFamilies = new Set(families);
  if (uniqueFamilies.size !== 2) {
    throw new Error('Sequence must include one Observability and one Pure step');
  }
  return families;
}

function findTwoStepSeq(node) {
  if (!node || typeof node !== 'object') {
    return null;
  }
  if (node.node === 'Seq' && Array.isArray(node.children) && node.children.length === 2) {
    return node;
  }
  if (Array.isArray(node.children)) {
    for (const child of node.children) {
      const found = findTwoStepSeq(child);
      if (found) {
        return found;
      }
    }
  }
  return null;
}

function sequenceExpression(families, inputName) {
  let expr = inputName;
  for (const family of families) {
    const symbol = family === 'Observability' ? 'E' : 'P';
    expr = `(${symbol} ${expr})`;
  }
  return expr;
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

function walkSome(node, predicate) {
  let result = false;
  walk(node, (current) => {
    if (result) {
      return;
    }
    if (predicate(current)) {
      result = true;
    }
  });
  return result;
}
