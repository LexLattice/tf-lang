const DEFAULT_OPTS = {
  requireIdempotencyKeyInTxn: true,
  forbidWritesOutsideTxn: false
};

export function checkTransactions(ir, catalog, opts = {}) {
  const options = { ...DEFAULT_OPTS, ...(opts || {}) };
  const reasons = [];

  function visit(node, insideTxn = false) {
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
    if (!isStorageWrite(node)) {
      return;
    }

    const primName = (node.prim || '').toLowerCase();

    if (insideTxn) {
      if (!options.requireIdempotencyKeyInTxn) {
        return;
      }
      const isCompareAndSwap = primName === 'compare-and-swap';
      const idemKey = node?.args?.idempotency_key;
      const hasIdemKey = typeof idemKey === 'string' && idemKey.length > 0;
      if (!isCompareAndSwap && !hasIdemKey) {
        reasons.push(`txn: ${primName} requires idempotency_key or compare-and-swap`);
      }
      return;
    }

    if (options.forbidWritesOutsideTxn) {
      reasons.push(`policy: ${primName} outside transaction`);
    }
  }

  function isStorageWrite(node) {
    const name = (node.prim || '').toLowerCase();
    if (!name) {
      return false;
    }

    const entry = lookupCatalogPrimitive(name);
    const effects = Array.isArray(entry?.effects) ? entry.effects : [];
    if (effects.some((effect) => String(effect).toLowerCase() === 'storage.write'.toLowerCase())) {
      return true;
    }

    return /^(write-object|delete-object|compare-and-swap)$/.test(name);
  }

  function lookupCatalogPrimitive(name) {
    const primitives = Array.isArray(catalog?.primitives) ? catalog.primitives : [];
    return (
      primitives.find((p) => (p.name || '').toLowerCase() === name) ||
      primitives.find((p) => (p.id || '').toLowerCase().endsWith(`/${name}@1`)) ||
      null
    );
  }

  visit(ir, false);

  return { ok: reasons.length === 0, reasons };
}
