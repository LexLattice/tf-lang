import { createServer } from 'http';
import { blake3 } from '@noble/hashes/blake3.js';
import { bytesToHex } from '@noble/hashes/utils.js';

function canonical(v: any): string {
  if (v === null) return 'null';
  if (typeof v === 'number') {
    if (!Number.isInteger(v)) throw new Error('E_L0_FLOAT');
    return String(v);
  }
  if (typeof v === 'string') return JSON.stringify(v);
  if (typeof v === 'boolean') return v ? 'true' : 'false';
  if (Array.isArray(v)) return '[' + v.map(canonical).join(',') + ']';
  if (typeof v === 'object') {
    const keys = Object.keys(v).sort();
    const entries = keys.map(k => JSON.stringify(k) + ':' + canonical((v as any)[k]));
    return '{' + entries.join(',') + '}';
  }
  throw new Error('E_L0_TYPE');
}

function canonicalJsonBytes(value: unknown): Uint8Array {
  return new TextEncoder().encode(canonical(value));
}

function applyDelta(state: any, delta: any): any {
  if (delta == null) return state;
  if (delta && typeof delta === 'object') {
    if ('replace' in delta) return delta.replace;
    if (Array.isArray(state) && 'append' in delta) return [...state, delta.append];
  }
  return state;
}

function makeEntry(value: any) {
  const canon = JSON.parse(canonical(value));
  const bytes = canonicalJsonBytes(canon);
  const id = bytesToHex(blake3(bytes));
  const entry: any = { id, value: canon };
  if (process.env.DEV_PROOFS === '1') entry.proof = 'dummy-proof';
  return entry;
}

function handlePlan(body: any) {
  const { world, plan } = body;
  const delta = plan ?? null;
  return { delta, world, journal: [makeEntry({ delta, from: 's0', to: 's1' })] };
}

function handleApply(body: any) {
  const { world } = body;
  const delta = body.delta ?? null;
  const world1 = applyDelta(world, delta);
  return { world: world1, journal: [makeEntry({ delta, from: 's0', to: 's1' })] };
}

export function createHostLite() {
  return createServer((req, res) => {
    if (req.method !== 'POST') {
      res.statusCode = 404;
      res.end();
      return;
    }
    const chunks: Buffer[] = [];
    req.on('data', c => chunks.push(c));
    req.on('end', () => {
      let body: any = {};
      try {
        body = chunks.length ? JSON.parse(Buffer.concat(chunks).toString()) : {};
      } catch {}
      let resp: any;
      if (req.url === '/plan') resp = handlePlan(body);
      else if (req.url === '/apply') resp = handleApply(body);
      else {
        res.statusCode = 404;
        res.end();
        return;
      }
      res.setHeader('content-type', 'application/json');
      res.end(JSON.stringify(resp));
    });
  });
}

