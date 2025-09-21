import { effectOf } from '../../tf-l0-check/src/effect-lattice.mjs';

export function emitParWriteSafety(ir, opts = {}) {
  const catalog = normalizeCatalog(opts.catalog);
  const hasConflict = detectParallelWriteConflict(ir, catalog);
  const lines = [];
  lines.push('(declare-sort URI 0)');
  lines.push('(declare-fun InParSameURI () Bool)');
  if (hasConflict) {
    lines.push('(assert InParSameURI)');
  } else {
    lines.push('(assert true)');
  }
  lines.push('(assert (not InParSameURI))');
  lines.push('(check-sat)');
  return lines.join('\n') + '\n';
}

export function emitCommutationEquiv(irSeqEP, irSeqPE, opts = {}) {
  const catalog = normalizeCatalog(opts.catalog);
  const analysisA = analyzeSequence(irSeqEP, catalog);
  const analysisB = analyzeSequence(irSeqPE, catalog);

  const lines = [];
  lines.push('(declare-sort Val 0)');
  lines.push('(declare-fun E (Val) Val)');
  lines.push('(declare-fun P (Val) Val)');
  lines.push('(assert (forall ((x Val)) (= (E (P x)) (P (E x)))))');
  lines.push('(declare-const x Val)');
  lines.push(`(define-fun outA () Val ${applySequence(analysisA.steps, 'x')})`);
  lines.push(`(define-fun outB () Val ${applySequence(analysisB.steps, 'x')})`);
  lines.push('(assert (not (= outA outB)))');
  lines.push('(check-sat)');
  return lines.join('\n') + '\n';
}

function detectParallelWriteConflict(ir, catalog) {
  let conflict = false;
  walk(ir, (node) => {
    if (conflict) {
      return;
    }
    if (!node || typeof node !== 'object') {
      return;
    }
    if (node.node === 'Par' && Array.isArray(node.children)) {
      const branchUris = node.children.map((child) => collectWriteUris(child, catalog));
      for (let i = 0; i < branchUris.length; i += 1) {
        const set = new Set(branchUris[i]);
        if (set.size === 0) {
          continue;
        }
        for (let j = i + 1; j < branchUris.length; j += 1) {
          for (const uri of branchUris[j]) {
            if (set.has(uri)) {
              conflict = true;
              return;
            }
          }
        }
      }
    }
  });
  return conflict;
}

function collectWriteUris(node, catalog) {
  const uris = [];
  walk(node, (current) => {
    if (!current || typeof current !== 'object') {
      return;
    }
    if (current.node !== 'Prim') {
      return;
    }
    const primId = selectPrimId(current);
    const family = effectOf(primId, catalog);
    if (family !== 'Storage.Write') {
      return;
    }
    const uri = selectUri(current.args);
    if (uri) {
      uris.push(uri);
    }
  });
  return dedupe(uris);
}

function analyzeSequence(ir, catalog) {
  if (!ir || typeof ir !== 'object') {
    throw new Error('Expected sequence IR object');
  }
  const steps = extractSequenceSteps(ir);
  if (steps.length !== 2) {
    throw new Error('Expected a two-step sequence');
  }
  const mapped = steps.map((node) => {
    const primId = selectPrimId(node);
    const family = effectOf(primId, catalog);
    if (family === 'Observability') {
      return 'E';
    }
    if (family === 'Pure') {
      return 'P';
    }
    throw new Error(`Unsupported effect family: ${family}`);
  });
  return { steps: mapped };
}

function applySequence(symbols, inputName) {
  let expr = inputName;
  for (const symbol of symbols) {
    expr = `(${symbol} ${expr})`;
  }
  return expr;
}

function extractSequenceSteps(ir) {
  if (ir.node === 'Seq' && Array.isArray(ir.children)) {
    return ir.children;
  }
  if (ir.node === 'Prim') {
    return [ir];
  }
  throw new Error('Expected Seq node with children');
}

function selectUri(args = {}) {
  if (!args || typeof args !== 'object') {
    return null;
  }
  const keys = ['uri', 'resource_uri', 'bucket_uri'];
  for (const key of keys) {
    const value = args[key];
    if (typeof value === 'string' && value.length > 0) {
      return value;
    }
  }
  return null;
}

function selectPrimId(node) {
  if (!node || typeof node !== 'object') {
    return '';
  }
  if (typeof node.prim_id === 'string' && node.prim_id.length > 0) {
    return node.prim_id;
  }
  if (typeof node.prim === 'string' && node.prim.length > 0) {
    return node.prim;
  }
  return '';
}

function walk(node, visitor) {
  if (Array.isArray(node)) {
    for (const entry of node) {
      walk(entry, visitor);
    }
    return;
  }
  if (!node || typeof node !== 'object') {
    return;
  }
  visitor(node);
  if (Array.isArray(node.children)) {
    for (const child of node.children) {
      walk(child, visitor);
    }
  }
  if (node.args && typeof node.args === 'object') {
    for (const value of Object.values(node.args)) {
      walk(value, visitor);
    }
  }
}

function dedupe(values) {
  return Array.from(new Set(values));
}

function normalizeCatalog(catalog) {
  if (!catalog || typeof catalog !== 'object') {
    return { primitives: [] };
  }
  if (!Array.isArray(catalog.primitives)) {
    return { primitives: [] };
  }
  return catalog;
}
