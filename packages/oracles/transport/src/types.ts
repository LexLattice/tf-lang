export interface TransportInput {
  readonly value: unknown;
}

export interface TransportMismatch {
  readonly pointer: string;
  readonly expected: unknown;
  readonly actual: unknown;
}

export interface TransportReport {
  readonly encoded: string;
}
