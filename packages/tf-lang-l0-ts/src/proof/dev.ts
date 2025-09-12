import type { ProofTag } from './tags.js';

export const log: ProofTag[] = [];

export function emit(tag: ProofTag): void {
  if (process?.env?.DEV_PROOFS === '1') {
    log.push(JSON.parse(JSON.stringify(tag)));
  }
}

export function take(): ProofTag[] {
  return log.splice(0, log.length);
}
