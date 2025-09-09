
import type { Claim, Evidence, Modality, PrecedenceCtx, PrecedenceFn, PrecedenceOrder, Scope } from 'claims-core-ts';
import { count, list } from 'claims-core-ts';

export interface Act {
  id: string;
  title: string;
  issuer: 'NATIONAL' | 'LOCAL';
  jurisdiction: string;          // e.g., 'RO' or 'RO/Bucuresti'
  in_force_from: string;         // ISO date
  in_force_to?: string | null;
  source_ref: string;
}

export interface Clause {
  id: string;
  act_id: string;
  path: string;
  text: string;
  jurisdiction: string;
  effective_from: string;
  effective_to?: string | null;
  source_ref: string;
}

export function inferModality(text: string): Modality | null {
  const t = text.toLowerCase();
  if (/(se interzice|este interzis|nu este permis)/.test(t)) return 'FORBIDDEN';
  if (/(este permis|se permite)/.test(t)) return 'PERMITTED';
  if (/(este obligatoriu|trebuie)/.test(t)) return 'OBLIGATORY';
  if (/(este exceptat|exceptie)/.test(t)) return 'EXEMPT';
  return null;
}

export function scopeFrom(cl: Clause): Scope {
  // Heuristic; in real code use NER/grammar
  return {
    subject: undefined,
    action: undefined,
    object: undefined,
    conditions: undefined,
    jurisdiction: cl.jurisdiction,
  };
}

export function toClaim(cl: Clause, datasetVersion: string): Claim | null {
  const m = inferModality(cl.text);
  if (!m) return null;
  const ev: Evidence = {
    source_uri: cl.source_ref,
    span: null,
    hash: String(Math.abs(hashCode(cl.text))),
    rule_id: 'regex.v1',
  };
  return {
    id: `${cl.id}`,
    kind: 'DEONTIC',
    modality: m,
    scope: scopeFrom(cl),
    effective: { from: cl.effective_from, to: cl.effective_to ?? null },
    status: ambiguousFromText(cl.text) ? 'ambiguous' : 'determinate',
    explanation: ambiguousFromText(cl.text) ? { why: 'contains modal hedge ("poate fi")', choice_points: ['modal hedge'] } : undefined,
    evidence: [ev],
    dataset_version: datasetVersion,
    query_hash: '0',
  };
}

export function ambiguousFromText(t: string): boolean {
  return /poate fi|poate fi interzis/.test(t.toLowerCase());
}

// Simple precedence: National > Local; newer > older; more specific jurisdiction > generic
export const legalPrecedence: PrecedenceFn = (a, b, _ctx: PrecedenceCtx): PrecedenceOrder => {
  const ja = a.scope.jurisdiction ?? '', jb = b.scope.jurisdiction ?? '';
  const ia = issuerFromJur(ja), ib = issuerFromJur(jb);
  if (ia !== ib) return rank(ia) > rank(ib) ? '>' : '<';
  // same issuer level → compare dates
  const da = a.effective.from, db = b.effective.from;
  if (da !== db) return da > db ? '>' : '<';
  // same date → specificity by path length of jurisdiction
  const sa = ja.split('/').length, sb = jb.split('/').length;
  if (sa !== sb) return sa > sb ? '>' : '<';
  // equal and unresolved
  return '⊥';
};

function issuerFromJur(j: string): 'NATIONAL' | 'LOCAL' {
  return j.includes('/') ? 'LOCAL' : 'NATIONAL';
}
function rank(x: 'NATIONAL' | 'LOCAL') { return x === 'NATIONAL' ? 2 : 1; }

function hashCode(s: string): number {
  let h = 0; for (let i=0;i<s.length;i++) { h = (h<<5)-h + s.charCodeAt(i) | 0; } return h;
}

// Convenience mini-API for demo
export function buildClaims(clauses: Clause[], datasetVersion: string): Claim[] {
  return clauses.map(c => toClaim(c, datasetVersion)).filter((x): x is Claim => !!x);
}

export const Query = { count, list };
