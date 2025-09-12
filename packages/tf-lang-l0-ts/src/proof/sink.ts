import type { ProofTag } from './tags.js';

const tags: ProofTag[] = [];

export function emit(tag: ProofTag): void {
  if (process.env.DEV_PROOFS === '1') tags.push(tag);
}

export function take(): ProofTag[] {
  const out = tags.slice();
  tags.length = 0;
  return out;
}
