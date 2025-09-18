export interface IdempotenceCase {
  readonly name: string;
  readonly note?: string;
  readonly once: unknown;
  readonly twice: unknown;
}

export interface IdempotenceInput {
  readonly cases?: ReadonlyArray<IdempotenceCase>;
}

export interface IdempotenceMismatch {
  readonly pointer: string;
  readonly left: unknown;
  readonly right: unknown;
}

export interface IdempotenceViolation {
  readonly caseName: string;
  readonly seed: string;
  readonly mismatch: IdempotenceMismatch;
}

export interface IdempotenceReport {
  readonly total: number;
  readonly passed: number;
  readonly failed: number;
  readonly firstFail?: IdempotenceMismatch;
}
