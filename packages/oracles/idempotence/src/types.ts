export interface IdempotenceInput {
  readonly cases?: ReadonlyArray<IdempotenceCase>;
}

export interface IdempotenceCase {
  readonly name: string;
  readonly description?: string;
  readonly once: unknown;
  readonly twice: unknown;
}

export interface IdempotenceReport {
  readonly casesChecked: number;
  readonly mismatches: ReadonlyArray<IdempotenceMismatch>;
}

export interface IdempotenceMismatch {
  readonly case: string;
  readonly pointer: string;
  readonly once: unknown;
  readonly twice: unknown;
}
