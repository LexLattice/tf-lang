
import type { Claim, Scope, PrecedenceFn, PrecedenceOrder } from './types.js';

export function scopeOverlaps(a: Scope, b: Scope): boolean {
  const same = (x?: string, y?: string) => !x || !y || x === y;
  return same(a.subject, b.subject)
      && same(a.action, b.action)
      && same(a.object, b.object)
      && same(a.jurisdiction, b.jurisdiction);
}

export function modalityOpposes(m1: string, m2: string): boolean {
  const opp = new Set(['FORBIDDEN|PERMITTED','PERMITTED|FORBIDDEN','OBLIGATORY|EXEMPT','EXEMPT|OBLIGATORY']);
  return opp.has(`${m1}|${m2}`);
}

export function precedenceOrder(a: Claim, b: Claim, ctx: any, fn: PrecedenceFn): PrecedenceOrder {
  return fn(a, b, ctx);
}

export function conflictDetect(claims: Claim[], ctx: any, fn: PrecedenceFn): { pair: [string,string], reason: string }[] {
  const out: { pair: [string,string], reason: string }[] = [];
  for (let i=0;i<claims.length;i++) for (let j=i+1;j<claims.length;j++) {
    const c1 = claims[i], c2 = claims[j];
    if (!scopeOverlaps(c1.scope, c2.scope)) continue;
    if (!modalityOpposes(c1.modality, c2.modality)) continue;
    const ord = precedenceOrder(c1, c2, ctx, fn);
    if (ord === '⊥') {
      out.push({ pair: [c1.id, c2.id], reason: 'unresolved precedence' });
    }
  }
  return out;
}
