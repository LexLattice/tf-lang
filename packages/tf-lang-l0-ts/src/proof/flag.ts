export const DEV_PROOFS: boolean = process.env.DEV_PROOFS === '1';

let cached: boolean | undefined;

export function devProofsEnabled(): boolean {
  if (cached === undefined) {
    cached = process.env.DEV_PROOFS === '1';
  }
  return cached;
}

export function resetDevProofsFlagForTest(): void {
  cached = undefined;
}
