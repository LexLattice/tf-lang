export interface OracleCtx {
  readonly seed: string;
  readonly now: number;
  canonicalize<T>(value: T): T;
}

export type MaybePromise<T> = T | Promise<T>;

export type OracleCheck<I, O> = (input: I, ctx: OracleCtx) => MaybePromise<OracleResult<O>>;

export interface Oracle<I, O> {
  readonly name: string;
  check(input: I, ctx: OracleCtx): Promise<OracleResult<O>>;
}

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

export interface OracleOk<T> {
  readonly ok: true;
  readonly value: T;
  readonly warnings?: readonly string[];
}

export type OracleResult<T> = OracleOk<T> | OracleFailure;

