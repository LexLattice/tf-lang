import type { RawResult } from './makeRawHandler.js';
import { canonicalJsonBytes, blake3hex } from 'tf-lang-l0';

export type LruCache = Map<string, Map<string, string>>;

const MAX_CACHE = 32;

function cacheLookup(cache: LruCache, world: string, key: string): string | undefined {
  const m = cache.get(world);
  if (!m) return undefined;
  const v = m.get(key);
  if (v !== undefined) {
    // LRU touch
    m.delete(key);
    m.set(key, v);
  }
  return v;
}

function cacheStore(cache: LruCache, world: string, key: string, canonResp: string) {
  let m = cache.get(world);
  if (!m) {
    m = new Map();
    cache.set(world, m);
  }
  if (m.has(key)) m.delete(key);
  m.set(key, canonResp);
  if (m.size > MAX_CACHE) {
    const fk = m.keys().next().value as string;
    m.delete(fk);
  }
}

export function makeHandler(deps: {
  exec: (world: string, plan: unknown) => Promise<unknown> | unknown;
  lru: LruCache;
}) {
  const { exec, lru } = deps;
  return async (method: string, url: string, body: any): Promise<RawResult> => {
    if (method !== 'POST') return { status: 404, body: { error: 'not_found' } };
    const action = url === '/plan' ? 'plan' : url === '/apply' ? 'apply' : null;
    if (!action) return { status: 404, body: { error: 'not_found' } };

    const key = action + ':' + blake3hex(canonicalJsonBytes(body));
    const wname = (body?.world ?? '') as string;
    const cached = cacheLookup(lru, wname, key);
    if (cached) return { status: 200, body: JSON.parse(cached) };

    const res = (await exec(wname, body?.plan)) as { world: unknown; delta: unknown; journal: unknown[] };
    const resp = { world: res.world, delta: res.delta, journal: res.journal };
    const canonResp = new TextDecoder().decode(canonicalJsonBytes(resp));
    cacheStore(lru, wname, key, canonResp);
    return { status: 200, body: JSON.parse(canonResp) };
  };
}

