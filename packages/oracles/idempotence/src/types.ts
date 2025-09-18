export interface IdempotenceInput {
  readonly cases?: ReadonlyArray<IdempotenceCase>;
}

export interface IdempotenceCase {
  readonly name: string;
  readonly seed?: string;
  readonly applications: ReadonlyArray<IdempotenceApplication>;
}

export interface IdempotenceApplication {
  readonly iteration: number;
  readonly value: unknown;
}

export interface IdempotenceReport {
  readonly casesChecked: number;
  readonly applicationsChecked: number;
}

export interface IdempotenceMismatch {
  readonly case: string;
  readonly seed?: string;
  readonly iteration: number;
  readonly pointer: string;
  readonly expected: unknown;
  readonly actual: unknown;
}
