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

const PURE = 'Pure';

function normalizePrimId(primId = '') {
  if (typeof primId !== 'string') {
    return '';
  }
  return primId.trim();
}

function fromCatalog(primId, catalog = {}) {
  const lookup = normalizePrimId(primId);
  if (!lookup) {
    return null;
  }
  const lower = lookup.toLowerCase();
  const primitives = Array.isArray(catalog?.primitives) ? catalog.primitives : [];
  const hit = primitives.find((p = {}) => {
    const id = typeof p.id === 'string' ? p.id.toLowerCase() : '';
    const name = typeof p.name === 'string' ? p.name.toLowerCase() : '';
    return id === lower || name === lower;
  });
  if (hit && Array.isArray(hit.effects) && hit.effects.length > 0) {
    const primary = hit.effects.find(e => typeof e === 'string' && e.length > 0);
    if (primary) {
      return primary;
    }
  }
  return null;
}

function heuristicFamily(primId) {
  const lookup = normalizePrimId(primId).toLowerCase();
  if (!lookup) {
    return PURE;
  }
  if (lookup === 'pure' || lookup.endsWith('/pure@1')) {
    return PURE;
  }
  if (/(metric|log|trace|observab)/.test(lookup)) {
    return 'Observability';
  }
  if (/(write|delete|update|insert|put|compare-and-swap|cas|remove|append)/.test(lookup)) {
    return 'Storage.Write';
  }
  if (/(read|list|get|fetch|load|select)/.test(lookup)) {
    return 'Storage.Read';
  }
  if (/(publish|request|ack|emit|send|notify|broadcast|post)/.test(lookup)) {
    return 'Network.Out';
  }
  if (/(subscribe|receive|listen|consume)/.test(lookup)) {
    return 'Network.In';
  }
  if (/(sign|verify|encrypt|decrypt|crypto|key)/.test(lookup)) {
    return 'Crypto';
  }
  if (/(policy|govern|authorize|compliance|audit)/.test(lookup)) {
    return 'Policy';
  }
  if (/(infra|infrastructure|deploy|provision|cluster|instance)/.test(lookup)) {
    return 'Infra';
  }
  if (/(time|clock|delay|wait|schedule)/.test(lookup)) {
    return 'Time';
  }
  if (/(ui|render|display|screen|interface|view)/.test(lookup)) {
    return 'UI';
  }
  return PURE;
}

export function effectOf(primId, catalog) {
  return fromCatalog(primId, catalog) ?? heuristicFamily(primId);
}

const COMMUTE_RULES = new Map([
  [PURE, new Set(EFFECT_FAMILIES)],
  ['Observability', new Set(['Observability', PURE])],
  ['Network.Out', new Set(['Observability', PURE])]
]);

export function canCommute(prevFamily, nextFamily) {
  const prev = typeof prevFamily === 'string' ? prevFamily : '';
  const next = typeof nextFamily === 'string' ? nextFamily : '';
  if (!prev || !next) {
    return false;
  }
  if (prev === PURE || next === PURE) {
    return true;
  }
  const allowed = COMMUTE_RULES.get(prev);
  if (!allowed) {
    return false;
  }
  return allowed.has(next);
}

import { conflict } from './footprints.mjs';

export function parSafe(famA, famB, ctx = {}) {
  const a = typeof famA === 'string' ? famA : '';
  const b = typeof famB === 'string' ? famB : '';
  if (a === 'Storage.Write' && b === 'Storage.Write') {
    const writesA = Array.isArray(ctx.writesA) ? ctx.writesA : [];
    const writesB = Array.isArray(ctx.writesB) ? ctx.writesB : [];
    if (typeof ctx.disjoint === 'function') {
      const allDisjoint = writesA.every((wa) => {
        const uriA = wa?.uri;
        return writesB.every((wb) => ctx.disjoint(uriA, wb?.uri));
      });
      if (allDisjoint) {
        return true;
      }
    }
    return !conflict(writesA, writesB);
  }
  return true;
}

export { EFFECT_FAMILIES };
