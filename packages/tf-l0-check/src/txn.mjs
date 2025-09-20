const DEFAULT_OPTS = {
  requireIdempotencyKeyInTxn: true,
  forbidWritesOutsideTxn: false
};

function lookupPrimitive(node, catalog = {}) {
  const primitives = Array.isArray(catalog.primitives) ? catalog.primitives : [];
  const name = (node.prim || '').toLowerCase();
  return primitives.find(p => {
    const id = p.id || '';
    return p.name === name || id.endsWith(`/${name}@1`);
  }) || null;
}

function hasStorageWriteEffect(primEntry) {
  if (!primEntry) return false;
  const effects = Array.isArray(primEntry.effects) ? primEntry.effects : [];
  return effects.includes('Storage.Write');
}

function isStorageWrite(node, catalog = {}) {
  if (!node || node.node !== 'Prim') return false;
  const name = (node.prim || '').toLowerCase();
  if (/^(write-object|delete-object|compare-and-swap)$/.test(name)) {
    return true;
  }
  const primEntry = lookupPrimitive(node, catalog);
  return hasStorageWriteEffect(primEntry);
}

function hasIdempotencyKey(node) {
  const key = node?.args?.idempotency_key;
  return typeof key === 'string' && key.length > 0;
}

export function checkTransactions(ir, catalog, opts = DEFAULT_OPTS) {
  const options = { ...DEFAULT_OPTS, ...(opts || {}) };
  const reasons = [];

  function visit(node, insideTxn) {
    if (!node || typeof node !== 'object') return;

    if (node.node === 'Region') {
      const isTxn = (node.kind || '').toLowerCase() === 'transaction';
      const nextInside = insideTxn || isTxn;
      for (const child of node.children || []) {
        visit(child, nextInside);
      }
      return;
    }

    if (node.node === 'Prim') {
      if (isStorageWrite(node, catalog)) {
        const name = (node.prim || '').toLowerCase();
        if (insideTxn) {
          const isCas = name === 'compare-and-swap';
          if (options.requireIdempotencyKeyInTxn && !isCas && !hasIdempotencyKey(node)) {
            reasons.push(`txn: ${name} requires idempotency_key or compare-and-swap`);
          }
        } else if (options.forbidWritesOutsideTxn) {
          reasons.push(`policy: ${name} outside transaction`);
        }
      }
      return;
    }

    if (Array.isArray(node.children)) {
      for (const child of node.children) {
        visit(child, insideTxn);
      }
    }
  }

  visit(ir, false);

  return { ok: reasons.length === 0, reasons };
}
