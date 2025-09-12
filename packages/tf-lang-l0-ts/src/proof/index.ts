export * from './tags.js';
import type { ProofTag } from './tags.js';
import { AsyncLocalStorage } from 'node:async_hooks';

let cached: boolean | undefined;
function devProofsEnabled(): boolean {
  if (cached === undefined) {
    cached = process.env.DEV_PROOFS === '1';
  }
  return cached;
}
export function resetDevProofsForTest(): void { cached = undefined; }

const store = new AsyncLocalStorage<ProofTag[]>();

export async function withProofLog<T>(fn: () => Promise<T> | T): Promise<{ result: T; proofs: ProofTag[] }> {
  if (!devProofsEnabled()) {
    return { result: await fn(), proofs: [] };
  }
  const buf: ProofTag[] = [];
  const result = await store.run(buf, fn);
  return { result, proofs: buf.slice() };
}

export function emit(tag: ProofTag): void {
  if (!devProofsEnabled()) return;
  const buf = store.getStore();
  if (!buf) throw new Error('DEV_PROOFS=1 but no proof log context');
  buf.push(tag);
}
