export interface TransportInput {
  readonly cases?: ReadonlyArray<TransportCase>;
}

export interface TransportCase {
  readonly name: string;
  readonly seed?: string;
  readonly value: unknown;
  readonly encoded?: string;
}

export interface TransportReport {
  readonly casesChecked: number;
  readonly roundTripsChecked: number;
}

export interface TransportDrift {
  readonly case: string;
  readonly seed?: string;
  readonly pointer: string;
  readonly before: unknown;
  readonly after: unknown;
  readonly error?: {
    readonly code: string;
    readonly message: string;
  };
}
