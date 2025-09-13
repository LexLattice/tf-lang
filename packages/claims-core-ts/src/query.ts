
import type { Claim } from './types.js';

export function count(claims: Claim[], where: Partial<Claim> & { at?: string } = {}) {
  const items = filter(claims, where);
  return { n: items.length, samples: items.slice(0, 10).map(c => c.id) };
}

export function list(claims: Claim[], where: Partial<Claim> & { at?: string } = {}) {
  const items = filter(claims, where);
  return { items };
}

export function filter(claims: Claim[], where: Partial<Claim> & { at?: string }) {
  const at = where.at ?? null;
  return claims.filter(c => {
    if (where.kind && c.kind !== where.kind) return false;
    if (where.modality && c.modality !== where.modality) return false;
    if (where.scope?.jurisdiction && c.scope.jurisdiction !== where.scope.jurisdiction) return false;
    if (at) {
      const fromOk = c.effective.from <= at;
      const toOk = !c.effective.to || at <= c.effective.to;
      if (!(fromOk && toOk)) return false;
    }
    return true;
  });
}
