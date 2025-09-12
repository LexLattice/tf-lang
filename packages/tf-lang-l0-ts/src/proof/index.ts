export * from './tags.js';
import type { ProofTag } from './tags.js';

const log: ProofTag[] = [];
let enabled: boolean | undefined;

/**
 * Returns true when DEV_PROOFS=1. First call reads the environment;
 * subsequent calls use a cached value for constant-time checks.
 */
export function devProofsEnabled(): boolean {
  if (enabled === undefined) {
    enabled = process.env.DEV_PROOFS === '1';
  }
  return enabled;
}

export function emit(tag: ProofTag): void {
  if (!devProofsEnabled()) return;
  log.push(tag);
}

export function flush(): ProofTag[] {
  const out = log.slice();
  log.length = 0;
  return out;
}

/** Test-only hook: clears cached flag and log so next call re-reads env. */
export function resetDevProofsForTest(): void {
  enabled = undefined;
  log.length = 0;
}
