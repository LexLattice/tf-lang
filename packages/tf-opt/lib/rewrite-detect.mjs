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
      for (const item of node) visit(item);
      return;
    }
    for (const key of Object.keys(node)) {
      if (key === 'node' || key === 'prim') continue;
      const value = node[key];
      if (value && typeof value === 'object') visit(value);
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
    if (!law) return;
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
    if (!next) continue;

    // Idempotent: x |> x
    if (current === next) {
      addObligation(`idempotent:${current}`, {
        rewrite: `idempotent:${current}@${i}`,
        positions: [i, i + 1],
        primitives: [current, next],
      });
    }

    // Inverse: serialize |> deserialize
    if (current === 'serialize' && next === 'deserialize') {
      addObligation('inverse:serialize-deserialize', {
        rewrite: `inverse:${current}->${next}@${i}`,
        positions: [i, i + 1],
        primitives: [current, next],
      });
    }

    // Commute: emit-metric with Pure
    const currentInfo = effectMap.get(current);
    const nextInfo = effectMap.get(next);

    if (current === 'emit-metric' && nextInfo && nextInfo.includes && nextInfo.includes('Pure')) {
      addObligation('commute:emit-metric-with-pure', {
        rewrite: `commute:emit-metric<->${next}@${i}`,
        positions: [i, i + 1],
        primitives: [current, next],
        direction: 'left',
      });
    }
    if (next === 'emit-metric' && currentInfo && currentInfo.includes && currentInfo.includes('Pure')) {
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
