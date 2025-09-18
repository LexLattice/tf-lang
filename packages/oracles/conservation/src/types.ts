export interface ConservationInput {
  readonly version?: string;
  readonly subject?: string;
  readonly keys?: ReadonlyArray<string>;
  readonly before?: Record<string, unknown>;
  readonly after?: Record<string, unknown>;
}

export interface ConservationReport {
  readonly keysChecked: number;
}

export interface ConservationViolation {
  readonly key: string;
  readonly before: unknown;
  readonly after: unknown;
  readonly delta: number | null;
}
