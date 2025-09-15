import { canonicalJsonBytes } from '../canon/json.js';

export interface Invariant {
  path: string;
  equals: unknown;
}

export interface Lens {
  path: string;
}

export interface TfSpec {
  version: string;
  goals: string[];
  invariants?: Invariant[];
  gates?: string[];
  lenses?: Lens[];
  effect?: unknown;
}

export function parseSpec(input: unknown): TfSpec {
  if (typeof input !== 'object' || input === null) {
    throw new Error('E_SPEC_TYPE');
  }
  const obj = input as Record<string, unknown>;
  const version = String(obj.version);
  if (!Array.isArray(obj.goals)) {
    throw new Error('E_SPEC_GOALS');
  }
  const goals = (obj.goals as unknown[]).map(g => String(g));
  const invRaw = (obj as { invariants?: unknown }).invariants;
  const invariants = Array.isArray(invRaw)
    ? invRaw.map(i => {
        const m = i as { path?: unknown; equals?: unknown };
        return { path: String(m.path), equals: m.equals };
      })
    : undefined;
  const gatesRaw = (obj as { gates?: unknown }).gates;
  const gates = Array.isArray(gatesRaw) ? gatesRaw.map(g => String(g)) : undefined;
  const lensesRaw = (obj as { lenses?: unknown }).lenses;
  const lenses = Array.isArray(lensesRaw)
    ? lensesRaw.map(l => {
        const m = l as { path?: unknown };
        return { path: String(m.path) };
      })
    : undefined;
  const effect = (obj as { effect?: unknown }).effect;
  const out: TfSpec = { version, goals };
  if (invariants) out.invariants = invariants;
  if (gates) out.gates = gates;
  if (lenses) out.lenses = lenses;
  if (effect !== undefined) out.effect = effect;
  return out;
}

export function canonicalSpec(spec: TfSpec): TfSpec {
  return spec;
}

export function serializeSpec(spec: TfSpec): Uint8Array {
  return canonicalJsonBytes(spec);
}
