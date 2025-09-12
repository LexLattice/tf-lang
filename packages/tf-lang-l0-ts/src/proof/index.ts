export * from './tags.js';
import type { ProofTag } from './tags.js';
import { AsyncLocalStorage } from 'node:async_hooks';
import { devProofsEnabled } from '../util/env.js';

const storage = new AsyncLocalStorage<ProofTag[]>();

export function withProofLog<T>(fn: () => T): T {
  return storage.run([], fn);
}

export function emit(tag: ProofTag): void {
  if (!devProofsEnabled()) return;
  const log = storage.getStore();
  if (log) log.push(tag);
}

export function flush(): ProofTag[] {
  const log = storage.getStore();
  if (!log) return [];
  const out = log.slice();
  log.length = 0;
  return out;
}
