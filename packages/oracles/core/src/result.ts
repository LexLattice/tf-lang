import type { Canonicalizer } from "./canonical.js";

export interface OracleError {
  readonly code: string;
  readonly explain: string;
  readonly details?: unknown;
}

export interface OracleFailure {
  readonly ok: false;
  readonly error: OracleError;
  readonly trace?: readonly string[];
}

export interface OracleSuccess<T> {
  readonly ok: true;
  readonly value: T;
  readonly warnings?: readonly string[];
}

export type OracleResult<T> = OracleSuccess<T> | OracleFailure;

export interface OracleCtx {
  readonly seed: string;
  readonly now: number;
  readonly canonicalize: Canonicalizer;
}

export type Oracle<I, O> = {
  check(input: I, ctx: OracleCtx): Promise<OracleResult<O>> | OracleResult<O>;
};

export function ok<T>(value: T, warnings?: Iterable<string>): OracleSuccess<T> {
  return {
    ok: true,
    value,
    ...(warnings ? { warnings: normalizeWarnings(warnings) } : {}),
  };
}

export function err(code: string, explain: string, details?: unknown): OracleFailure {
  return {
    ok: false,
    error: {
      code: normalizeCode(code),
      explain: explain.trim(),
      ...(details === undefined ? {} : { details }),
    },
  };
}

export function withTrace(base: OracleFailure, trace: Iterable<string>): OracleFailure {
  const existing = base.trace ?? [];
  const merged = normalizeWarnings([...existing, ...trace]);
  if (merged.length === 0) {
    return { ...base, trace: undefined };
  }
  return {
    ...base,
    trace: merged,
  };
}

function normalizeWarnings(source: Iterable<string>): string[] {
  const set = new Set<string>();
  for (const entry of source) {
    const normalized = entry.trim();
    if (normalized.length > 0) {
      set.add(normalized);
    }
  }
  return Array.from(set.values());
}

function normalizeCode(code: string): string {
  const normalized = code.trim();
  if (!normalized) {
    return "E_UNKNOWN";
  }
  return normalized.toUpperCase();
}
