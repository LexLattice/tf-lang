export class XorShift32 {
  private state: number;
  constructor(seed: number) { this.state = (seed|0) || 0x9E3779B9; }
  next(): number { let x=this.state|0; x^=x<<13; x^=x>>>17; x^=x<<5; this.state=x|0; return ((x>>>0)/0x100000000); }
  nextInt(): number { return (this.next()*0x100000000)>>>0; }
}
export class FixedClock {
  private epochNs: bigint;
  constructor(epochMs: number) { this.epochNs = BigInt(epochMs) * 1_000_000n; }
  nowNs(): bigint { return this.epochNs; }
}
