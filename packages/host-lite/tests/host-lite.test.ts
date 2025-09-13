import { describe, it, expect } from 'vitest';
import { makeHandler, createHost, createNodeHandler } from '../src/server.js';
import { canonicalJsonBytes, blake3hex } from 'tf-lang-l0';
import { readFile } from 'node:fs/promises';
import { IncomingMessage, ServerResponse } from 'node:http';
import { PassThrough } from 'node:stream';

const td = new TextDecoder();

interface JournalEntry { canon: string; proof?: string }
interface Resp { world: unknown; delta: unknown; journal: JournalEntry[] }

describe('host-lite', () => {
  it('idempotent plan and apply', async () => {
    const host = createHost();
    const handler = makeHandler(host);
    const body = { world: 'w', plan: 1 };
    const p1 = await handler('POST', '/plan', body);
    const p2 = await handler('POST', '/plan', body);
    expect(p1.status).toBe(200);
    expect(p2.status).toBe(200);
    expect(p1.body).toEqual(p2.body);
    const a1 = await handler('POST', '/apply', body);
    const a2 = await handler('POST', '/apply', body);
    expect(a1.body).toEqual(a2.body);
  });

  it('canonical journal and proof gating', async () => {
    const body = { world: 'c', plan: 2 };
    delete process.env.DEV_PROOFS;
    const h0 = makeHandler(createHost());
    const r0 = await h0('POST', '/apply', body);
    const j0 = (r0.body as Resp).journal[0];
    expect(j0.proof).toBeUndefined();
    const canon0 = td.decode(canonicalJsonBytes(JSON.parse(j0.canon)));
    expect(canon0).toBe(j0.canon);

    process.env.DEV_PROOFS = '1';
    const h1 = makeHandler(createHost());
    const r1 = await h1('POST', '/apply', body);
    const j1 = (r1.body as Resp).journal[0];
    const canon1 = td.decode(canonicalJsonBytes(JSON.parse(j1.canon)));
    expect(canon1).toBe(j1.canon);
    const hash = blake3hex(canonicalJsonBytes(JSON.parse(j1.canon)));
    expect(j1.proof).toBe(hash);
    delete process.env.DEV_PROOFS;
  });

  it('state is ephemeral', async () => {
    const h1 = makeHandler(createHost());
    await h1('POST', '/apply', { world: 'e', plan: 3 });
    const r1 = await h1('POST', '/plan', { world: 'e', plan: 0 });
    const w1 = (r1.body as Resp).world;

    const h2 = makeHandler(createHost());
    const r2 = await h2('POST', '/plan', { world: 'e', plan: 0 });
    const w2 = (r2.body as Resp).world;
    expect(w1).not.toEqual(w2);
  });

  it('404 for unknown path', async () => {
    const handler = makeHandler(createHost());
    const r = await handler('POST', '/nope', {});
    expect(r.status).toBe(404);
    const canon = td.decode(canonicalJsonBytes(r.body));
    expect(canon).toBe('{"error":"not_found"}');
  });

  it('404 for wrong method', async () => {
    const handler = makeHandler(createHost());
    const r = await handler('GET', '/plan', {});
    expect(r.status).toBe(404);
    const canon = td.decode(canonicalJsonBytes(r.body));
    expect(canon).toBe('{"error":"not_found"}');
  });

  it('bounded cache prevents growth', async () => {
    const host = createHost();
    const handler = makeHandler(host);
    for (let i = 0; i < 40; i++) {
      await handler('POST', '/plan', { world: 'm', plan: i });
    }
    const worldCache = host.cache.get('m');
    expect(worldCache?.size ?? 0).toBeLessThanOrEqual(32);
  });

  it('multi-world cache bounds', async () => {
    const host = createHost();
    const handler = makeHandler(host);
    for (let w = 0; w < 4; w++) {
      for (let i = 0; i < 40; i++) {
        await handler('POST', '/plan', { world: `mw${w}`, plan: i });
      }
    }
    for (let w = 0; w < 4; w++) {
      const worldCache = host.cache.get(`mw${w}`);
      expect(worldCache?.size ?? 0).toBeLessThanOrEqual(32);
    }
  });

  it('400 for malformed JSON', async () => {
    const handler = createNodeHandler();
    const req = new IncomingMessage(new PassThrough());
    req.method = 'POST';
    req.url = '/plan';
    const res = new ServerResponse(req);
    let body = '';
    res.end = (chunk?: unknown) => {
      if (chunk) body += Buffer.from(chunk as Uint8Array).toString();
      res.emit('finish');
    };
    const finished = new Promise((resolve) => res.on('finish', resolve));
    handler(req, res);
    req.emit('data', Buffer.from('{'));
    req.emit('end');
    await finished;
    expect(res.statusCode).toBe(400);
    expect(body).toBe('{"error":"bad_request"}');
  });

  it('no deep imports across packages', async () => {
    const src = await readFile(new URL('../src/server.ts', import.meta.url), 'utf8');
    expect(src.includes('../')).toBe(false);
  });
});
