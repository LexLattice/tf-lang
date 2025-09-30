import {
  canonicalLawName,
  canonicalPrimitiveName,
  loadPrimitiveEffectMap,
  isKnownLaw,
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
  const effectMap = await loadPrimitiveEffectMap();
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
    };
    obligations.push(entry);
    encounteredLaws.add(law);
  };

  for (let i = 0; i < names.length; i += 1) {
    const current = names[i];
    const next = names[i + 1];
    if (!next) continue;

    // Idempotent: x |> x (only for known idempotent laws)
    if (current === next) {
      const candidate = `idempotent:${current}`;
      if (isKnownLaw(candidate)) {
        addObligation(candidate, {
          rewrite: `${candidate}@${i}`,
          positions: [i, i + 1],
          primitives: [current, next],
        });
      }
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
    const currentEff = effectMap.get(current);   // effects[] or undefined
    const nextEff = effectMap.get(next);
    if (current === 'emit-metric' && Array.isArray(nextEff) && nextEff.includes('Pure')) {
      addObligation('commute:emit-metric-with-pure', {
        rewrite: `commute:emit-metric<->${next}@${i}`,
        positions: [i, i + 1],
        primitives: [current, next],
        direction: 'left',
      });
    }
    // Only emit the LEFT-direction obligation to avoid reintroducing
    // commute obligations after applying a swap.
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
