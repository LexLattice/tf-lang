import { isKnownLaw } from './data.mjs';

function normalizeForStableStringify(value) {
  if (Array.isArray(value)) {
    return value.map(normalizeForStableStringify);
  }
  if (value && typeof value === 'object') {
    const next = {};
    for (const key of Object.keys(value).sort()) {
      next[key] = normalizeForStableStringify(value[key]);
    }
    return next;
  }
  return value;
}

export function stableStringify(value) {
  return JSON.stringify(normalizeForStableStringify(value), null, 2);
}

export function normalizeRewriteEntries(entries = []) {
  const dedupe = new Map();
  const unknownLaws = new Set();
  for (const entry of entries || []) {
    if (!entry || typeof entry !== 'object') continue;
    const law = typeof entry.law === 'string' ? entry.law.trim() : '';
    const rewrite = typeof entry.rewrite === 'string' ? entry.rewrite.trim() : '';
    if (!law || !rewrite) continue;
    if (!isKnownLaw(law)) {
      unknownLaws.add(law);
      continue;
    }
    const key = `${rewrite}\u0000${law}`;
    if (!dedupe.has(key)) {
      dedupe.set(key, { law, rewrite });
    }
  }

  if (unknownLaws.size > 0) {
    throw new Error(`unknown law(s): ${Array.from(unknownLaws).sort().join(', ')}`);
  }

  const sorted = Array.from(dedupe.values());
  sorted.sort((a, b) => {
    const rewriteCmp = a.rewrite.localeCompare(b.rewrite);
    if (rewriteCmp !== 0) return rewriteCmp;
    return a.law.localeCompare(b.law);
  });

  return sorted;
}

export function buildUsedLawManifest({ plans = [], extras = [] } = {}) {
  const usedLawSet = new Set();
  const rewriteEntries = [];

  for (const plan of plans || []) {
    if (!plan || typeof plan !== 'object') continue;
    if (Array.isArray(plan.used_laws)) {
      for (const law of plan.used_laws) {
        if (typeof law !== 'string') continue;
        const trimmed = law.trim();
        if (trimmed) usedLawSet.add(trimmed);
      }
    }
    if (Array.isArray(plan.rewrites)) {
      rewriteEntries.push(...plan.rewrites);
    }
  }

  for (const group of extras || []) {
    if (!group) continue;
    const iterable = Array.isArray(group) || group instanceof Set ? group : [];
    for (const law of iterable) {
      if (typeof law !== 'string') continue;
      const trimmed = law.trim();
      if (trimmed) usedLawSet.add(trimmed);
    }
  }

  const used_laws = Array.from(usedLawSet).sort();
  const rewrites = normalizeRewriteEntries(rewriteEntries);

  if (used_laws.some((law) => !isKnownLaw(law))) {
    const unknown = used_laws.filter((law) => !isKnownLaw(law));
    throw new Error(`unknown law(s): ${unknown.sort().join(', ')}`);
  }

  const manifest = { used_laws };
  if (rewrites.length > 0) {
    manifest.rewrites = rewrites;
  }
  return manifest;
}
