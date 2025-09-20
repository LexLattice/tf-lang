const DEFAULT_OPTS = {
  requireIdempotencyKeyInTxn: true,
  forbidWritesOutsideTxn: false
};

export function checkTransactions(ir, catalog, opts = DEFAULT_OPTS) {
  const reasons = [];
  const options = { ...DEFAULT_OPTS, ...(opts || {}) };

  function visit(node, insideTxn) {
    if (!node || typeof node !== 'object') {
      return;
    }

    if (node.node === 'Region') {
      const nextInside = insideTxn || node.kind === 'Transaction';
      for (const child of node.children || []) {
        visit(child, nextInside);
      }
      return;
    }

    if (node.node === 'Prim') {
      handlePrim(node, insideTxn);
      return;
    }

    for (const child of node.children || []) {
      visit(child, insideTxn);
    }
  }

  function handlePrim(node, insideTxn) {
    if (!isStorageWrite(node, catalog)) {
      return;
    }

    const primName = (node.prim || '').toLowerCase();

    if (insideTxn) {
      if (!options.requireIdempotencyKeyInTxn) {
        return;
      }

      if (primName === 'compare-and-swap') {
        return;
      }

      const key = node.args?.idempotency_key;
      if (typeof key !== 'string' || key.length === 0) {
        reasons.push(`txn: ${primName} requires idempotency_key or compare-and-swap`);
      }
      return;
    }

    if (options.forbidWritesOutsideTxn) {
      reasons.push(`policy: ${primName} outside transaction`);
    }
  }

  visit(ir, false);
  return { ok: reasons.length === 0, reasons };
}

function isStorageWrite(node, catalog) {
  const primName = (node.prim || '').toLowerCase();
  const effects = lookupEffects(primName, catalog);
  if ((effects || []).includes('Storage.Write')) {
    return true;
  }
  return /^(write-object|delete-object|compare-and-swap)$/.test(primName);
}

function lookupEffects(primName, catalog) {
  if (!catalog || !catalog.primitives) {
    return [];
  }
  const hit = catalog.primitives.find(p => {
    const name = (p.name || '').toLowerCase();
    const id = (p.id || '').toLowerCase();
    return name === primName || id.endsWith(`/${primName}@1`);
  });
  return hit?.effects || [];
}
