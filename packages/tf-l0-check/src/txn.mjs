const NAME_BASED_WRITE = /^(write-object|delete-object|compare-and-swap)$/;
const SPECIAL_REGEX_CHARS = /[.*+?^${}()|[\]\\]/g;

const DEFAULT_OPTS = {
  requireIdempotencyKeyInTxn: true,
  forbidWritesOutsideTxn: false,
  onFallbackToNameDetection: undefined
};

export function checkTransactions(ir, catalog, opts = {}) {
  const options = { ...DEFAULT_OPTS, ...(opts || {}) };
  const reasons = [];

  function visit(node, insideTxn = false) {
    if (node == null) {
      return;
    }

    if (Array.isArray(node)) {
      for (const child of node) {
        visit(child, insideTxn);
      }
      return;
    }

    if (typeof node !== 'object') {
      return;
    }

    if (node.node === 'Prim') {
      handlePrim(node, insideTxn);
    }

    const isTxnRegion = node.node === 'Region' && node.kind === 'Transaction';
    const nextInside = insideTxn || isTxnRegion;
    const children = Array.isArray(node.children) ? node.children : [];

    for (const child of children) {
      visit(child, nextInside);
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
    if (entry) {
      const effects = Array.isArray(entry.effects) ? entry.effects : [];
      return effects.includes('Storage.Write');
    }

    if (NAME_BASED_WRITE.test(name)) {
      options.onFallbackToNameDetection?.();
      return true;
    }

    return false;
  }

  function lookupCatalogPrimitive(name) {
    const primitives = Array.isArray(catalog?.primitives) ? catalog.primitives : [];
    if (primitives.length === 0) {
      return null;
    }

    const lowerName = name.toLowerCase();
    const byName = primitives.find((p) => (p.name || '').toLowerCase() === lowerName);
    if (byName) {
      return byName;
    }

    const idRegex = new RegExp(`/${escapeRegex(lowerName)}@\\d+$`, 'i');
    for (const prim of primitives) {
      const id = prim?.id;
      if (typeof id === 'string' && idRegex.test(id)) {
        return prim;
      }
    }

    return null;
  }

  visit(ir, false);

  return { ok: reasons.length === 0, reasons };
}

function escapeRegex(value) {
  return value.replace(SPECIAL_REGEX_CHARS, '\\$&');
}
