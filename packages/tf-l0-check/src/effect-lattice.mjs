import { conflict as footprintConflict } from './footprints.mjs';

export const CANONICAL_EFFECT_FAMILIES = Object.freeze([
  'Pure',
  'Observability',
  'Storage.Read',
  'Storage.Write',
  'Network.In',
  'Network.Out',
  'Crypto',
  'Policy',
  'Infra',
  'Time',
  'UI'
]);

export const EFFECT_PRECEDENCE = Object.freeze([
  'Pure',
  'Observability',
  'Network.Out',
  'Storage.Read',
  'Storage.Write',
  'Crypto',
  'Policy',
  'Infra',
  'Time',
  'UI'
]);

const FAMILY_ALIASES = Object.freeze({
  'Time.Read': 'Time',
  'Time.Wait': 'Time',
  'Randomness.Read': 'Infra'
});

const NORMALIZATION_MAP = new Map(
  CANONICAL_EFFECT_FAMILIES.map(family => [family.toLowerCase(), family])
);

for (const [alias, canonical] of Object.entries(FAMILY_ALIASES)) {
  NORMALIZATION_MAP.set(alias.toLowerCase(), canonical);
}

export const EFFECT_FAMILIES = CANONICAL_EFFECT_FAMILIES;

const FALLBACK_RULES = [
  { re: /(emit-metric|trace-span|log-event)/i, family: 'Observability' },
  { re: /(read|list)/i, family: 'Storage.Read' },
  { re: /(write|delete|compare-and-swap)/i, family: 'Storage.Write' },
  { re: /(publish|request|acknowledge)/i, family: 'Network.Out' },
  { re: /subscribe/i, family: 'Network.In' },
  { re: /(encrypt|decrypt|sign|verify|derive-key|manage-secret|generate-key)/i, family: 'Crypto' },
  { re: /(authorize|policy)/i, family: 'Policy' },
  { re: /(now|sleep|time)/i, family: 'Time' },
  { re: /(hash|encode|decode|serialize|deserialize|compress|decompress|chunk|assemble|transform)/i, family: 'Pure' },
  { re: /(ui|render)/i, family: 'UI' },
  { re: /(infra|provision)/i, family: 'Infra' }
];

function nameFromId(primId = '') {
  if (typeof primId !== 'string') {
    return '';
  }
  const match = /^tf:[^/]+\/([^@]+)@/.exec(primId);
  if (match) {
    return match[1];
  }
  const parts = primId.split('/');
  return parts[parts.length - 1] || primId;
}

export function normalizeFamily(family) {
  if (typeof family !== 'string') {
    return 'Pure';
  }
  const trimmed = family.trim();
  if (trimmed.length === 0) {
    return 'Pure';
  }
  const mapped = NORMALIZATION_MAP.get(trimmed.toLowerCase());
  if (mapped) {
    return mapped;
  }
  return 'Pure';
}

export function effectRank(family) {
  const normalized = normalizeFamily(family);
  const index = EFFECT_PRECEDENCE.indexOf(normalized);
  return index === -1 ? Number.MAX_SAFE_INTEGER : index;
}

export function effectOf(primId, catalog = {}) {
  const primitives = Array.isArray(catalog.primitives) ? catalog.primitives : [];
  const name = nameFromId(primId).toLowerCase();
  const lowerId = (primId || '').toLowerCase();
  const entry = primitives.find(p => {
    const pid = (p.id || '').toLowerCase();
    const pname = (p.name || '').toLowerCase();
    return pid === lowerId || pname === name;
  }) || null;

  const declared = Array.isArray(entry?.effects) && entry.effects.length > 0 ? entry.effects[0] : null;
  if (declared) {
    return normalizeFamily(declared);
  }

  for (const rule of FALLBACK_RULES) {
    if (rule.re.test(name)) {
      return normalizeFamily(rule.family);
    }
  }

  return 'Pure';
}

export function canCommute(prevFamily, nextFamily) {
  const prev = normalizeFamily(prevFamily);
  const next = normalizeFamily(nextFamily);

  if (prev === 'Pure' || next === 'Pure') {
    return true;
  }

  if (prev === 'Observability') {
    return next === 'Observability' || next === 'Network.Out';
  }

  if (prev === 'Network.Out') {
    return next === 'Observability';
  }

  return false;
}

export function commuteSymmetric(familyA, familyB) {
  return canCommute(familyA, familyB) && canCommute(familyB, familyA);
}

export function parSafe(famA, famB, ctx = {}) {
  const a = normalizeFamily(famA);
  const b = normalizeFamily(famB);

  if (a === 'Storage.Write' && b === 'Storage.Write') {
    const writesA = Array.isArray(ctx.writesA) ? ctx.writesA : null;
    const writesB = Array.isArray(ctx.writesB) ? ctx.writesB : null;

    if (typeof ctx.disjoint === 'function' && writesA && writesB) {
      const urisA = extractUris(writesA);
      const urisB = extractUris(writesB);
      if (urisA.length === 0 && urisB.length === 0) {
        return false;
      }
      for (const uriA of urisA) {
        for (const uriB of urisB) {
          if (!ctx.disjoint(uriA, uriB)) {
            return false;
          }
        }
      }
      return true;
    }

    if (!writesA || !writesB) {
      return false;
    }

    const conflictFn = typeof ctx.conflict === 'function' ? ctx.conflict : footprintConflict;
    return !conflictFn(writesA, writesB);
  }

  return true;
}

export function primaryFamily(effects = []) {
  if (!effects || effects.length === 0) {
    return 'Pure';
  }
  if (effects.length === 1) {
    return normalizeFamily(effects[0]);
  }
  return null;
}

function extractUris(writes = []) {
  return (writes || [])
    .filter(entry => entry && entry.mode !== 'read')
    .map(entry => entry.uri)
    .filter(uri => typeof uri === 'string');
}
