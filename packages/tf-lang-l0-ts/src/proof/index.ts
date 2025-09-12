export * from './tags.js';
import type { ProofTag } from './tags.js';

const log: ProofTag[] = [];

export function emit(tag: ProofTag): void {
  if (process.env.DEV_PROOFS === '1') {
    log.push(tag);
  }
}

export function flush(): ProofTag[] {
  const out = log.slice();
  log.length = 0;
  return out;
}
