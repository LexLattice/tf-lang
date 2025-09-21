import { conflict } from './footprints.mjs';

export const EFFECT_FAMILIES = Object.freeze([
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

const FALLBACK_EFFECTS = new Map([
  ['read-object', 'Storage.Read'],
  ['list-objects', 'Storage.Read'],
  ['write-object', 'Storage.Write'],
  ['delete-object', 'Storage.Write'],
  ['compare-and-swap', 'Storage.Write'],
  ['publish', 'Network.Out'],
  ['request', 'Network.Out'],
  ['acknowledge', 'Network.Out'],
  ['subscribe', 'Network.In'],
  ['emit-metric', 'Observability'],
  ['emit-log', 'Observability'],
  ['sign-data', 'Crypto'],
  ['verify-signature', 'Crypto'],
  ['encrypt', 'Crypto'],
  ['decrypt', 'Crypto'],
  ['authorize', 'Policy'],
  ['hash', 'Pure'],
  ['serialize', 'Pure'],
  ['deserialize', 'Pure']
]);

const FAMILY_NORMALIZATION = new Map([
  ['Time.Read', 'Time'],
  ['Time.Wait', 'Time'],
  ['Randomness.Read', 'Crypto']
]);

function normalizeFamily(value) {
  if (typeof value !== 'string' || value.length === 0) {
    return 'Pure';
  }
  const normalized = FAMILY_NORMALIZATION.get(value) || value;
  if (EFFECT_FAMILIES.includes(normalized)) {
    return normalized;
  }
  return 'Pure';
}

function catalogLookup(primId, catalog) {
  if (!catalog || typeof catalog !== 'object') {
    return null;
  }
  const primitives = Array.isArray(catalog.primitives) ? catalog.primitives : [];
  const query = (primId || '').toLowerCase();
  return (
    primitives.find(primitive => (primitive.id || '').toLowerCase() === query) ||
    primitives.find(primitive => (primitive.name || '').toLowerCase() === query) ||
    primitives.find(primitive => (primitive.id || '').toLowerCase().endsWith(`/${query}@1`)) ||
    null
  );
}

function fallbackEffect(primId) {
  const key = (primId || '')
    .toLowerCase()
    .replace(/^.*[:/]/, '')
    .replace(/@\d+$/, '');
  return FALLBACK_EFFECTS.get(key) || 'Pure';
}

export function effectOf(primId, catalog) {
  const entry = catalogLookup(primId, catalog);
  if (entry && Array.isArray(entry.effects) && entry.effects.length > 0) {
    const preferred = entry.effects.includes('Pure') ? 'Pure' : entry.effects[0];
    return normalizeFamily(preferred);
  }
  return normalizeFamily(fallbackEffect(primId));
}

const COMMUTES = new Map([
  ['Pure', new Set(EFFECT_FAMILIES)],
  ['Observability', new Set(['Pure', 'Observability'])],
  ['Network.Out', new Set(['Pure', 'Observability'])]
]);

export function canCommute(familyA, familyB) {
  const a = normalizeFamily(familyA);
  const b = normalizeFamily(familyB);
  if (a === 'Pure' || b === 'Pure') {
    return true;
  }
  const rules = COMMUTES.get(a);
  return rules ? rules.has(b) : false;
}

export function parSafe(familyA, familyB, ctx = {}) {
  const a = normalizeFamily(familyA);
  const b = normalizeFamily(familyB);
  if (a === 'Storage.Write' && b === 'Storage.Write') {
    const writesA = Array.isArray(ctx.writesA) ? ctx.writesA : [];
    const writesB = Array.isArray(ctx.writesB) ? ctx.writesB : [];
    if (typeof ctx.disjoint === 'function' && writesA.length && writesB.length) {
      for (const left of writesA) {
        for (const right of writesB) {
          const uriA = left?.uri;
          const uriB = right?.uri;
          if (ctx.disjoint(uriA, uriB) === true) {
            continue;
          }
          if (uriA && uriB && uriA === uriB) {
            return false;
          }
          return false;
        }
      }
      return true;
    }
    if (writesA.length && writesB.length) {
      return !conflict(writesA, writesB);
    }
    return false;
  }
  return true;
}
