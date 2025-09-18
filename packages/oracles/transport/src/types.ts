export interface TransportInput {
  readonly version?: string;
  readonly subject?: string;
  readonly cases?: ReadonlyArray<TransportCase>;
}

export interface TransportCase {
  readonly name?: string;
  readonly seed?: string;
  readonly encoded?: string;
  readonly value?: unknown;
}

export interface TransportReport {
  readonly casesChecked: number;
  readonly roundTripsChecked: number;
}

export interface TransportMismatch {
  readonly case?: string;
  readonly seed?: string;
  readonly pointer: string;
  readonly expected: unknown;
  readonly actual: unknown;
}
