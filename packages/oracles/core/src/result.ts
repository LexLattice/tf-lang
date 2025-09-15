import { canonicalize } from "./canonical.js";
import type {
  OracleError,
  OracleFailure,
  OracleOk,
  OracleResult,
} from "./types.js";

const collator = new Intl.Collator("en", { sensitivity: "variant" });

const uniqueSorted = (items: Iterable<string>): string[] => {
  const seen = new Set<string>();
  for (const item of items) {
    const trimmed = item.trim();
    if (trimmed.length === 0) continue;
    seen.add(trimmed);
  }
  return [...seen].sort((a, b) => collator.compare(a, b));
};

const normalizeTrace = (trace: Iterable<string> | undefined): string[] | undefined => {
  if (!trace) return undefined;
  const normalized = uniqueSorted(trace);
  return normalized.length > 0 ? normalized : undefined;
};

const withWarnings = <T>(value: T, warnings: Iterable<string>): OracleOk<T> => {
  const normalized = uniqueSorted(warnings);
  if (normalized.length === 0) {
    return { ok: true, value };
  }
  return { ok: true, value, warnings: normalized };
};

export const ok = <T>(value: T, warnings: Iterable<string> = []): OracleOk<T> =>
  withWarnings(value, warnings);

export const mergeWarnings = <T>(result: OracleOk<T>, warnings: Iterable<string>): OracleOk<T> =>
  withWarnings(result.value, [...(result.warnings ?? []), ...warnings]);

export const error = (
  code: string,
  explain: string,
  details?: unknown,
): OracleError => ({
  code,
  explain,
  ...(typeof details === "undefined" ? {} : { details: canonicalize(details) }),
});

export const failure = (
  code: string,
  explain: string,
  options: { details?: unknown; trace?: Iterable<string> } = {},
): OracleFailure => {
  const err = error(code, explain, options.details);
  const trace = normalizeTrace(options.trace);
  if (!trace) {
    return { ok: false, error: err };
  }
  return { ok: false, error: err, trace };
};

export const fromError = (
  err: OracleError,
  trace?: Iterable<string>,
): OracleFailure => {
  const normalizedTrace = normalizeTrace(trace);
  if (!normalizedTrace) {
    return { ok: false, error: canonicalize(err) } as OracleFailure;
  }
  return { ok: false, error: canonicalize(err) as OracleError, trace: normalizedTrace };
};

export const isOk = <T>(result: OracleResult<T>): result is OracleOk<T> => result.ok;

export const formatFailure = (result: OracleResult<unknown>): string => {
  if (result.ok) return "ok";
  const base = `${result.error.code}: ${result.error.explain}`;
  if (!result.error.details) return base;
  return `${base} | details=${JSON.stringify(result.error.details)}`;
};

export const mapValue = <A, B>(result: OracleResult<A>, mapper: (value: A) => B): OracleResult<B> => {
  if (!result.ok) return result;
  const mapped = mapper(result.value);
  if (result.warnings) {
    return { ok: true, value: mapped, warnings: [...result.warnings] };
  }
  return { ok: true, value: mapped };
};

