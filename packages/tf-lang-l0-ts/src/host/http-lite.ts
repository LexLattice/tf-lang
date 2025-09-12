import { createServer } from 'node:http';
import { canonicalJsonBytes } from '../canon/json.js';
import { blake3hex } from '../canon/hash.js';
import { DummyHost } from './memory.js';
import { devProofsEnabled, flush } from '../proof/index.js';

export function createHostLite() {
  const worlds = new Map<string, any[]>();
  const cache = new Map<string, Buffer>();

  const server = createServer(async (req, res) => {
    if (req.method !== 'POST' || (req.url !== '/plan' && req.url !== '/apply')) {
      res.statusCode = 404;
      res.end();
      return;
    }

    const chunks: Buffer[] = [];
    for await (const chunk of req) chunks.push(chunk as Buffer);
    let body: any;
    try {
      body = JSON.parse(Buffer.concat(chunks).toString());
    } catch {
      res.statusCode = 400;
      res.end();
      return;
    }
    if (typeof body.world !== 'string') {
      res.statusCode = 400;
      res.end();
      return;
    }
    const key = blake3hex(canonicalJsonBytes({ url: req.url, body }));
    if (cache.has(key)) {
      const buf = cache.get(key)!;
      res.statusCode = 200;
      res.setHeader('content-type', 'application/json');
      res.end(buf);
      return;
    }

    const state0 = structuredClone(worlds.get(body.world) ?? []);
    const delta = await DummyHost.call_tf('tf://plan/delta@0.1', [state0, body.plan]);
    const state1 = await DummyHost.diff_apply(state0, delta);
    const snap0 = await DummyHost.snapshot_make(state0);
    const id0 = await DummyHost.snapshot_id(snap0);
    const snap1 = await DummyHost.snapshot_make(state1);
    const id1 = await DummyHost.snapshot_id(snap1);
    const entry = await DummyHost.journal_record(body.plan, delta, id0, id1, null);

    const result: any = { world: state1, delta, journal: entry.value };
    const proofs = flush();
    if (devProofsEnabled()) result.proofs = proofs;
    const buf = Buffer.from(canonicalJsonBytes(result));
    cache.set(key, buf);
    if (req.url === '/apply') {
      worlds.set(body.world, state1);
    }

    res.statusCode = 200;
    res.setHeader('content-type', 'application/json');
    res.end(buf);
  });

  return server;
}
