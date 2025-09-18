export interface TransportInput {
  readonly version?: string;
  readonly subject?: string;
  readonly cases?: ReadonlyArray<TransportCase>;
  readonly json?: string;
  readonly value?: unknown;
}

export interface TransportCase {
  readonly name?: string;
  readonly seed?: string;
  readonly json?: string;
  readonly value?: unknown;
}

export interface TransportReport {
  readonly casesChecked: number;
}

export interface TransportDrift {
  readonly case?: string;
  readonly seed?: string;
  readonly pointer: string;
  readonly expected: unknown;
  readonly actual: unknown;
}
