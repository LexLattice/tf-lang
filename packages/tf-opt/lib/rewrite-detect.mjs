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
  const obligations = [];
  const lawSet = new Set();

  for (let i = 1; i < seq.length; i += 1) {
    const prev = seq[i - 1];
    const curr = seq[i];
    if (isEmitMetricHashPair(prev, curr)) {
      obligations.push({
        law: COMMUTE_EMIT_METRIC_LAW,
        span: [i - 1, i],
        primitives: [prev, curr],
      });
      lawSet.add(COMMUTE_EMIT_METRIC_LAW);
    }
  }

  return {
    primitives: [...seq],
    obligations,
    rewritesApplied: obligations.length,
    laws: Array.from(lawSet).sort(),
=======
import {
  canonicalLawName,
  canonicalPrimitiveName,
  loadLawAliasSet,
  loadPrimitiveEffectMap,
} from './data.mjs';

export function extractPrimitivesFromIr(ir) {
  const collected = [];
  const visit = (node) => {
    if (!node || typeof node !== 'object') return;
    if (node.node === 'Prim' && typeof node.prim === 'string') {
      const prim = canonicalPrimitiveName(node.prim);
      collected.push(prim);
      return;
    }
    if (Array.isArray(node)) {
      for (const item of node) {
        visit(item);
      }
      return;
    }
    for (const key of Object.keys(node)) {
      if (key === 'node' || key === 'prim') continue;
      const value = node[key];
      if (value && typeof value === 'object') {
        visit(value);
      }
    }
  };
  visit(ir);
  return collected;
}

export async function analyzePrimitiveSequence(primitives) {
  const [lawSet, effectMap] = await Promise.all([
    loadLawAliasSet(),
    loadPrimitiveEffectMap(),
  ]);
  const names = primitives
    .map((name) => canonicalPrimitiveName(name))
    .filter((name) => name.length > 0);
  const obligations = [];
  const encounteredLaws = new Set();

  const addObligation = (rawLaw, details) => {
    const law = canonicalLawName(rawLaw);
    if (!law) {
      return;
    }
    const rewrite = typeof details.rewrite === 'string' ? details.rewrite : `${law}@${obligations.length}`;
    const entry = {
      law,
      rewrite,
      positions: Array.isArray(details.positions) ? [...details.positions] : [],
      primitives: Array.isArray(details.primitives) ? [...details.primitives] : [],
      direction: details.direction ?? null,
      known: lawSet.has(law),
    };
    obligations.push(entry);
    encounteredLaws.add(law);
  };

  for (let i = 0; i < names.length; i += 1) {
    const current = names[i];
    const next = names[i + 1];
    if (!next) {
      continue;
    }

    if (current === next) {
      addObligation(`idempotent:${current}`, {
        rewrite: `idempotent:${current}@${i}`,
        positions: [i, i + 1],
        primitives: [current, next],
      });
    }

    if (current === 'serialize' && next === 'deserialize') {
      addObligation('inverse:serialize-deserialize', {
        rewrite: `inverse:${current}->${next}@${i}`,
        positions: [i, i + 1],
        primitives: [current, next],
      });
    }

    const currentInfo = effectMap.get(current);
    const nextInfo = effectMap.get(next);

    if (current === 'emit-metric' && nextInfo && nextInfo.effect === 'Pure') {
      addObligation('commute:emit-metric-with-pure', {
        rewrite: `commute:emit-metric<->${next}@${i}`,
        positions: [i, i + 1],
        primitives: [current, next],
        direction: 'left',
      });
    }
    if (next === 'emit-metric' && currentInfo && currentInfo.effect === 'Pure') {
      addObligation('commute:emit-metric-with-pure', {
        rewrite: `commute:${current}<->emit-metric@${i}`,
        positions: [i, i + 1],
        primitives: [current, next],
        direction: 'right',
      });
    }
  }

  const laws = Array.from(encounteredLaws).sort((a, b) => a.localeCompare(b));
  const summary = { laws, rewritesApplied: obligations.length };

  return {
    primitives: names,
    obligations,
    laws,
    rewritesApplied: obligations.length,
    summary,
  };
}
