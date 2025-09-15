export interface OracleOk<T> {
  ok: true;
  value: T;
  warnings?: string[];
}

export interface OracleErrorDetail {
  code: string;
  explain: string;
  details?: unknown;
}

export interface OracleErr {
  ok: false;
  error: OracleErrorDetail;
  trace?: string[];
}

export type OracleOutcome<T> = OracleOk<T> | OracleErr;

export interface ErrorOptions {
  readonly details?: unknown;
  readonly trace?: readonly string[];
}

export function ok<T>(value: T, warnings: readonly string[] = []): OracleOk<T> {
  if (warnings.length === 0) {
    return { ok: true, value };
  }
  return { ok: true, value, warnings: [...warnings] };
}

export function err(
  code: string,
  explain: string,
  options: ErrorOptions = {}
): OracleErr {
  const payload: OracleErr = {
    ok: false,
    error: { code, explain },
  };

  if (typeof options.details !== "undefined") {
    payload.error.details = options.details;
  }
  if (options.trace && options.trace.length > 0) {
    payload.trace = [...options.trace];
  }
  return payload;
}
