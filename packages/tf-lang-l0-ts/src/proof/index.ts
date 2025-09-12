export * from './tags.js';
import type { ProofTag } from './tags.js';

const log: ProofTag[] = [];
let enabled: boolean | undefined;

export function devProofsEnabled(): boolean {
  if (enabled === undefined) {
    enabled = process.env.DEV_PROOFS === '1';
  }
  return enabled;
}

export function resetDevProofsForTest(): void {
  enabled = undefined;
  log.length = 0;
}

export function emit(tag: ProofTag): void {
  // callers check devProofsEnabled()
  log.push(tag);
}

export function flush(): ProofTag[] {
  const out = log.slice();
  log.length = 0;
  return out;
}
