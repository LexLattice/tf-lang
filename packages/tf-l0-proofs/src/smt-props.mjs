import { effectOf } from '../../tf-l0-check/src/effect-lattice.mjs';

export function emitParWriteSafety(ir, opts = {}) {
  const catalog = normalizeCatalog(opts.catalog);
  const hasConflict = detectParallelWriteConflict(ir, catalog);
  const lines = [];
  lines.push('; par write safety');
  lines.push('(declare-sort URI 0)');
  lines.push('(declare-fun InParSameURI () Bool)');
  lines.push('; safety axiom: parallel writes to the same URI are illegal');
  lines.push('(assert (not InParSameURI))');
  lines.push('; IR encoding: does the flow contain parallel same-URI writes?');
  lines.push(`(assert (= InParSameURI ${hasConflict ? 'true' : 'false'}))`);
  lines.push('(check-sat)');
  return lines.join('\n') + '\n';
}

export function emitCommutationEquiv(irSeqEP, irSeqPE, opts = {}) {
  const catalog = normalizeCatalog(opts.catalog);
  const analysisA = analyzeSequence(irSeqEP, catalog);
  const analysisB = analyzeSequence(irSeqPE, catalog);

  const lines = [];
  lines.push('; observability/pure commutation equivalence');
  lines.push('(declare-sort Val 0)');
  lines.push('(declare-fun E (Val) Val)');
  lines.push('(declare-fun P (Val) Val)');
  lines.push('; commutation law: Observability commutes with Pure');
  lines.push('(assert (forall ((x Val)) (= (E (P x)) (P (E x)))))');
  lines.push('; IR encoding: sequence outputs over a shared symbolic input');
  lines.push('(declare-const x Val)');
  lines.push(`(define-fun outA () Val ${applySequence(analysisA.steps, 'x')})`);
  lines.push(`(define-fun outB () Val ${applySequence(analysisB.steps, 'x')})`);
  lines.push('; goal: assume the outputs differ');
  lines.push('(assert (not (= outA outB)))');
  lines.push('(check-sat)');
  return lines.join('\n') + '\n';
}

function detectParallelWriteConflict(ir, catalog) {
  const stack = [ir];
  while (stack.length > 0) {
    const node = stack.pop();
    if (!node || typeof node !== 'object') {
      continue;
    }
    if (node.node === 'Par' && Array.isArray(node.children)) {
      const branchUris = node.children.map((child) => collectBranchWriteUris(child, catalog));
      if (hasOverlap(branchUris)) {
        return true;
      }
    }
    if (Array.isArray(node.children)) {
      for (const child of node.children) {
        stack.push(child);
      }
    }
  }
  return false;
}

function collectBranchWriteUris(node, catalog, uris = new Set()) {
  if (!node || typeof node !== 'object') {
    return uris;
  }
  if (node.node === 'Prim' && isStorageWritePrim(node, catalog)) {
    const uri = selectUri(node.args);
    if (uri) {
      uris.add(uri);
    }
  }
  if (Array.isArray(node.children)) {
    for (const child of node.children) {
      collectBranchWriteUris(child, catalog, uris);
    }
  }
  return uris;
}

function hasOverlap(branchSets) {
  for (let i = 0; i < branchSets.length; i += 1) {
    const current = branchSets[i];
    if (!current || current.size === 0) {
      continue;
    }
    for (let j = i + 1; j < branchSets.length; j += 1) {
      const other = branchSets[j];
      if (!other || other.size === 0) {
        continue;
      }
      for (const uri of current) {
        if (other.has(uri)) {
          return true;
        }
      }
    }
  }
  return false;
}

function analyzeSequence(ir, catalog) {
  if (!ir || typeof ir !== 'object' || ir.node !== 'Seq' || !Array.isArray(ir.children)) {
    throw new Error(SEQUENCE_VALIDATION_ERROR);
  }
  if (ir.children.length !== 2) {
    throw new Error(SEQUENCE_VALIDATION_ERROR);
  }
  const steps = ir.children;
  if (!steps.every((step) => step && typeof step === 'object' && step.node === 'Prim')) {
    throw new Error(SEQUENCE_VALIDATION_ERROR);
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
    throw new Error(SEQUENCE_VALIDATION_ERROR);
  });
  if (new Set(mapped).size !== 2) {
    throw new Error(SEQUENCE_VALIDATION_ERROR);
  }
  return { steps: mapped };
}

function applySequence(symbols, inputName) {
  let expr = inputName;
  for (const symbol of symbols) {
    expr = `(${symbol} ${expr})`;
  }
  return expr;
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

function isStorageWritePrim(node, catalog) {
  const primId = selectPrimId(node);
  const family = effectOf(primId, catalog);
  if (family === 'Storage.Write') {
    return true;
  }
  return isNamedAsStorageWrite(primId);
}

function isNamedAsStorageWrite(primId) {
  if (typeof primId !== 'string' || primId.length === 0) {
    return false;
  }
  const lower = primId.toLowerCase();
  return (
    lower.includes('write-object') ||
    lower.includes('delete-object') ||
    lower.includes('compare-and-swap')
  );
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

const SEQUENCE_VALIDATION_ERROR =
  'error: commute expects two Seq[Prim,Prim] with effects {Observability,Pure}.';
