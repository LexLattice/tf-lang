export * from './tags.js';
import type { ProofTag } from './tags.js';

let log: ProofTag[] = [];

function initEmit(tag: ProofTag): void {
  if (process.env.DEV_PROOFS === '1') {
    log.push(tag);
    emitImpl = (t: ProofTag): void => {
      log.push(t);
    };
  } else {
    emitImpl = () => {};
  }
}

let emitImpl: (tag: ProofTag) => void = initEmit;

export function emit(tag: ProofTag): void {
  emitImpl(tag);
}

export function flush(): ProofTag[] {
  const out = log;
  log = [];
  return out;
}

// test-only: reset cache and log
/**
 * Reset cached env flag and log (test-only).
 */
export function reset(): void {
  log = [];
  emitImpl = initEmit;
}
