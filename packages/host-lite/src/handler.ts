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

type ExecResult = { world: unknown; delta: unknown; journal: unknown[] };

export function makeHandler(deps: {
  exec: (world: string, plan: unknown) => Promise<ExecResult> | ExecResult;
  commit: (world: string, state: unknown) => void;
  cache: LruCache;
}) {
  const { exec, commit, cache } = deps;
  const td = new TextDecoder();
  return async (method: string, url: string, body: unknown): Promise<RawResult> => {
    // DRY routing here
    if (method !== 'POST') return { status: 404, body: { error: 'not_found' } };
    const action = url === '/plan' ? 'plan' : url === '/apply' ? 'apply' : null;
    if (!action) return { status: 404, body: { error: 'not_found' } };

    // Validate body.world
    const b = body as { world?: unknown; plan?: unknown };
    const wname = typeof b?.world === 'string' ? b.world : '';
    if (!wname) return { status: 400, body: { error: 'bad_request' } };

    // Cache key per action and canonical body (hash to keep key compact)
    const key = action + ':' + blake3hex(canonicalJsonBytes(body));
    const cached = cacheLookup(cache, wname, key);
    if (cached) return { status: 200, body: JSON.parse(cached) };

    // Compute via shared exec
    const res = await exec(wname, b.plan);
    if (action === 'apply') {
      // Persist new world state
      commit(wname, res.world);
    }
    const out = { world: res.world, delta: res.delta, journal: res.journal };
    const canon = td.decode(canonicalJsonBytes(out));
    cacheStore(cache, wname, key, canon);
    return { status: 200, body: JSON.parse(canon) };
  };
}
