import http from 'node:http';
import { canonicalJsonBytes } from '../../tf-lang-l0-ts/src/canon/json.js';
import { blake3hex } from '../../tf-lang-l0-ts/src/canon/hash.js';
import { DummyHost } from '../../tf-lang-l0-ts/src/host/memory.js';
import { devProofsEnabled } from '../../tf-lang-l0-ts/src/proof/index.js';

export function createServer() {
  let world: any = [];
  const planCache = new Map<string, Uint8Array>();
  const applyCache = new Map<string, Uint8Array>();

  return http.createServer(async (req, res) => {
    if (req.method !== 'POST') {
      res.statusCode = 404;
      return res.end();
    }
    let body = '';
    req.on('data', chunk => { body += chunk; });
    req.on('end', async () => {
      try {
        const obj = body ? JSON.parse(body) : {};
        const key = Buffer.from(canonicalJsonBytes(obj)).toString('hex');
        if (req.url === '/plan') {
          let payload = planCache.get(key);
          if (!payload) {
            const sim: any = await DummyHost.call_tf('tf://plan/simulate@0.1', [world, obj.plan]);
            const out = { delta: sim.delta, world: sim.world };
            payload = canonicalJsonBytes(out);
            planCache.set(key, payload);
          }
          res.statusCode = 200;
          res.setHeader('content-type', 'application/json');
          return res.end(payload);
        }
        if (req.url === '/apply') {
          let payload = applyCache.get(key);
          if (!payload) {
            const delta: any = await DummyHost.call_tf('tf://plan/delta@0.1', [world, obj.plan]);
            const snap0 = await DummyHost.snapshot_make(world);
            const id0 = await DummyHost.snapshot_id(snap0);
            world = await DummyHost.diff_apply(world, delta);
            const snap1 = await DummyHost.snapshot_make(world);
            const id1 = await DummyHost.snapshot_id(snap1);
            const entry: any = await DummyHost.journal_record(obj.plan, delta, id0, id1, {});
            const resObj: any = { world, journal: entry };
            if (devProofsEnabled()) {
              resObj.proof = blake3hex(canonicalJsonBytes(entry));
            }
            payload = canonicalJsonBytes(resObj);
            applyCache.set(key, payload);
          }
          res.statusCode = 200;
          res.setHeader('content-type', 'application/json');
          return res.end(payload);
        }
        res.statusCode = 404;
        res.end();
      } catch {
        res.statusCode = 500;
        res.end();
      }
    });
  });
}
