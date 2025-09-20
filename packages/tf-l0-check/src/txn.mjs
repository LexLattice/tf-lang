export function checkTransactions(ir, catalog, opts = {}) {
  const {
    requireIdempotencyKeyInTxn = true,
    forbidWritesOutsideTxn = false
  } = opts || {};

  const reasons = [];

  function visit(node, insideTxn) {
    if (!node || typeof node !== 'object') {
      return;
    }

    if (node.node === 'Region') {
      const kind = (node.kind || '').toLowerCase();
      const nextInside = insideTxn || kind === 'transaction';
      for (const child of node.children || []) {
        visit(child, nextInside);
      }
      return;
    }

    if (node.node === 'Prim') {
      const name = (node.prim || '').toLowerCase();
      if (!name) {
        return;
      }

      if (isStorageWrite(name, catalog)) {
        if (insideTxn) {
          if (
            requireIdempotencyKeyInTxn &&
            name !== 'compare-and-swap'
          ) {
            const key = node.args?.idempotency_key;
            const hasKey = typeof key === 'string' && key.trim().length > 0;
            if (!hasKey) {
              reasons.push(`txn: ${name} requires idempotency_key or compare-and-swap`);
            }
          }
        } else if (forbidWritesOutsideTxn) {
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

function isStorageWrite(name, catalog) {
  if (!name) {
    return false;
  }

  const primitives = catalog?.primitives || [];
  const hit = primitives.find(p => {
    const pname = (p.name || '').toLowerCase();
    if (pname === name) {
      return true;
    }
    const id = (p.id || '').toLowerCase();
    return id.endsWith(`/${name}@1`);
  });

  if (hit && Array.isArray(hit.effects)) {
    const hasEffect = hit.effects.some(e => (e || '').toLowerCase() === 'storage.write');
    if (hasEffect) {
      return true;
    }
  }

  return /^(write-object|delete-object|compare-and-swap)$/.test(name);
}
