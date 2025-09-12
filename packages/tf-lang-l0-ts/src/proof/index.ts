export * from './tags.js';
import type { ProofTag } from './tags.js';
import { devProofsEnabled } from '../util/env';

const log: ProofTag[] = [];

export function emit(tag: ProofTag): void {
  if (devProofsEnabled()) {
    log.push(tag);
  }
}

export function flush(): ProofTag[] {
  const out = log.slice();
  log.length = 0;
  return out;
}
