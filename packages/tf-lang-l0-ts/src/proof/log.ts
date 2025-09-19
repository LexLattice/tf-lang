import type { ProofTag } from './tags.js';
import { devProofsEnabled, resetDevProofsFlagForTest } from './flag.js';

const log: ProofTag[] = [];

export function emit(tag: ProofTag): void {
  if (!devProofsEnabled()) return;
  log.push(tag);
}

export function flush(): ProofTag[] {
  const out = log.slice();
  log.length = 0;
  return out;
}

export function resetDevProofsForTest(): void {
  resetDevProofsFlagForTest();
  log.length = 0;
}
