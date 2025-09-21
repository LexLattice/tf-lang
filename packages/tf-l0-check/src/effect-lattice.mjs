import { conflict } from './footprints.mjs';

const EFFECT_FAMILIES = [
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
];

const FALLBACK_RULES = [
  { re: /(emit|log|metric|trace|observability)/, family: 'Observability' },
  { re: /(read|list)-object/, family: 'Storage.Read' },
  { re: /(write|delete)-object|compare-and-swap/, family: 'Storage.Write' },
  { re: /(publish|request|acknowledge|notify|send)/, family: 'Network.Out' },
  { re: /(subscribe|listen|receive)/, family: 'Network.In' },
  { re: /(sign|verify|encrypt|decrypt|crypto)/, family: 'Crypto' },
  { re: /policy/, family: 'Policy' },
  { re: /(infra|infrastructure|provision)/, family: 'Infra' },
  { re: /(time|clock|sleep|wait)/, family: 'Time' },
  { re: /(ui|render|display|view)/, family: 'UI' }
];

const COMMUTE_TABLE = new Map([
  ['Observability', new Set(['Pure', 'Observability'])],
  ['Storage.Write', new Set()],
  ['Storage.Read', new Set()],
  ['Network.In', new Set()],
  ['Network.Out', new Set(['Pure', 'Observability'])],
  ['Crypto', new Set()],
  ['Policy', new Set()],
  ['Infra', new Set()],
  ['Time', new Set()],
  ['UI', new Set()],
  ['Pure', new Set(EFFECT_FAMILIES)]
]);

function normalizePrimId(primId = '') {
  const lower = primId.toLowerCase();
  const tail = lower.split('/').pop() || lower;
  const afterColon = tail.split(':').pop() || tail;
  const withoutVersion = afterColon.split('@')[0];
  return withoutVersion;
}

export function effectOf(primId, catalog = {}) {
  const primitives = Array.isArray(catalog?.primitives) ? catalog.primitives : [];
  const normalized = normalizePrimId(primId);
  const loweredId = (primId || '').toLowerCase();
  const match =
    primitives.find(p => (p.id || '').toLowerCase() === loweredId) ||
    primitives.find(p => (p.name || '').toLowerCase() === normalized) ||
    primitives.find(p => normalizePrimId(p.id || '') === normalized);

  const effects = Array.isArray(match?.effects) ? match.effects : [];
  const resolved = effects.find(e => e !== 'Pure') || effects[0];
  if (resolved) {
    return resolved;
  }

  for (const { re, family } of FALLBACK_RULES) {
    if (re.test(normalized)) {
      return family;
    }
  }
  return 'Pure';
}

export function canCommute(famA, famB) {
  if (!famA || !famB) {
    return false;
  }
  if (famA === 'Pure' || famB === 'Pure') {
    return true;
  }
  const row = COMMUTE_TABLE.get(famA);
  if (!row) {
    return false;
  }
  return row.has(famB);
}

export function parSafe(famA, famB, ctx = {}) {
  if (famA !== 'Storage.Write' || famB !== 'Storage.Write') {
    return true;
  }
  const writesA = Array.isArray(ctx.writesA) ? ctx.writesA : [];
  const writesB = Array.isArray(ctx.writesB) ? ctx.writesB : [];
  const disjoint = typeof ctx.disjoint === 'function' ? ctx.disjoint : null;

  if (disjoint && writesA.length && writesB.length) {
    let allDisjoint = true;
    for (const a of writesA) {
      for (const b of writesB) {
        if (!disjoint(a?.uri, b?.uri)) {
          allDisjoint = false;
          break;
        }
      }
      if (!allDisjoint) {
        break;
      }
    }
    if (allDisjoint) {
      return true;
    }
  }

  if (!writesA.length || !writesB.length) {
    return false;
  }

  return !conflict(writesA, writesB);
}

export { EFFECT_FAMILIES };
