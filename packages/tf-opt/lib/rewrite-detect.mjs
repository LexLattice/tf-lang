const COMMUTE_EMIT_METRIC_LAW = 'commute:emit-metric-with-pure';
const HASH_PRIM = 'hash';
const EMIT_METRIC_PRIM = 'emit-metric';

function canonicalPrimitiveName(value) {
  return typeof value === 'string' ? value.toLowerCase() : '';
}

export function extractPrimitivesFromIr(ir, acc = []) {
  if (!ir || typeof ir !== 'object') {
    return acc;
  }

  if (ir.node === 'Prim') {
    const name = canonicalPrimitiveName(ir.prim);
    if (name) {
      acc.push(name);
    }
  }

  for (const value of Object.values(ir)) {
    if (Array.isArray(value)) {
      for (const item of value) {
        extractPrimitivesFromIr(item, acc);
      }
    } else if (value && typeof value === 'object') {
      extractPrimitivesFromIr(value, acc);
    }
  }

  return acc;
}

function isEmitMetricHashPair(a, b) {
  return (
    (a === HASH_PRIM && b === EMIT_METRIC_PRIM) ||
    (a === EMIT_METRIC_PRIM && b === HASH_PRIM)
  );
}

export async function analyzePrimitiveSequence(seq) {
  let rewritesApplied = 0;
  const laws = new Set();

  for (let i = 1; i < seq.length; i += 1) {
    if (isEmitMetricHashPair(seq[i - 1], seq[i])) {
      rewritesApplied += 1;
      laws.add(COMMUTE_EMIT_METRIC_LAW);
    }
  }

  return {
    rewritesApplied,
    laws: Array.from(laws).sort(),
  };
}
