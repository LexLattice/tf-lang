import { effectOf } from '../../tf-l0-check/src/effect-lattice.mjs';

export function emitParWriteSafety(ir, opts = {}) {
  const hasSameUri = hasParallelSameUriWrite(ir, opts.catalog || {});
  const lines = [];
  lines.push('(declare-sort URI 0)');
  lines.push('(declare-fun InParSameURI () Bool)');
  if (hasSameUri) {
    lines.push('(assert InParSameURI)');
  }
  lines.push('(assert (not InParSameURI))');
  lines.push('(check-sat)');
  return lines.join('\n') + '\n';
}

export function emitCommutationEquiv(irSeqEP, irSeqPE, opts = {}) {
  const catalog = opts.catalog || {};
  const seqA = findSeqNode(irSeqEP);
  const seqB = findSeqNode(irSeqPE);
  const stepsA = extractSequenceSteps(seqA, catalog);
  const stepsB = extractSequenceSteps(seqB, catalog);
  const inputName = 'input';
  const lines = [];
  lines.push('(declare-sort Val 0)');
  lines.push('(declare-fun E (Val) Val)');
  lines.push('(declare-fun P (Val) Val)');
  lines.push('(assert (forall ((x Val)) (= (E (P x)) (P (E x)))))');
  lines.push(`(declare-const ${inputName} Val)`);
  lines.push(`(define-fun outA () Val ${composeSteps(stepsA, inputName)})`);
  lines.push(`(define-fun outB () Val ${composeSteps(stepsB, inputName)})`);
  lines.push('(assert (not (= outA outB)))');
  lines.push('(check-sat)');
  return lines.join('\n') + '\n';
}

function hasParallelSameUriWrite(ir, catalog) {
  let found = false;
  walk(ir, (node) => {
    if (found || !node || typeof node !== 'object') {
      return;
    }
    if (node.node === 'Par' && Array.isArray(node.children)) {
      const branchUris = node.children.map((child) => collectWriteUris(child, catalog));
      for (let i = 0; i < branchUris.length && !found; i++) {
        const left = branchUris[i];
        if (left.size === 0) {
          continue;
        }
        for (let j = i + 1; j < branchUris.length && !found; j++) {
          const right = branchUris[j];
          if (right.size === 0) {
            continue;
          }
          for (const uri of left) {
            if (right.has(uri)) {
              found = true;
              break;
            }
          }
        }
      }
    }
  });
  return found;
}

function collectWriteUris(node, catalog) {
  const uris = new Set();
  const visit = (current) => {
    if (!current || typeof current !== 'object') {
      return;
    }
    if (current.node === 'Prim' && isStorageWrite(current, catalog)) {
      const uri = extractUri(current);
      if (uri) {
        uris.add(uri);
      }
    }
    if (Array.isArray(current.children)) {
      for (const child of current.children) {
        visit(child);
      }
    }
  };
  visit(node);
  return uris;
}

function isStorageWrite(node, catalog) {
  const primId = typeof node?.prim === 'string' ? node.prim : '';
  if (!primId) {
    return false;
  }
  const family = effectOf(primId, catalog);
  return family === 'Storage.Write';
}

function extractUri(node) {
  const uri = node?.args?.uri;
  return typeof uri === 'string' && uri.length > 0 ? uri : null;
}

function findSeqNode(ir) {
  if (!ir || typeof ir !== 'object') {
    return null;
  }
  if (ir.node === 'Seq') {
    return ir;
  }
  if (Array.isArray(ir.children)) {
    for (const child of ir.children) {
      const found = findSeqNode(child);
      if (found) {
        return found;
      }
    }
  }
  return null;
}

function extractSequenceSteps(seqNode, catalog) {
  if (!seqNode || seqNode.node !== 'Seq' || !Array.isArray(seqNode.children)) {
    throw new Error('Expected a Seq node with children');
  }
  const steps = [];
  for (const child of seqNode.children) {
    if (child && child.node === 'Prim') {
      const symbol = effectSymbol(effectOf(child.prim, catalog));
      steps.push(symbol);
    }
  }
  if (steps.length !== 2) {
    throw new Error('Commutation property expects a two-step sequence');
  }
  return steps;
}

function effectSymbol(family) {
  switch (family) {
    case 'Observability':
      return 'E';
    case 'Pure':
      return 'P';
    default:
      throw new Error(`Unsupported effect family for commutation: ${family}`);
  }
}

function composeSteps(steps, inputName) {
  let expr = inputName;
  for (const step of steps) {
    expr = `(${step} ${expr})`;
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
