import test from 'node:test';
import assert from 'node:assert/strict';

import { createInmemAdapters } from '../packages/tf-l0-codegen-ts/src/adapters/inmem.mjs';
import { runtimeFromAdapters } from '../packages/tf-l0-codegen-ts/src/runtime/run-ir.mjs';

const encoder = new TextEncoder();

test('network publish appends entries for inspection', async () => {
  const instance = createInmemAdapters();
  await instance.adapters.publish('events', 'run-1', '{"ok":true}');
  await instance.adapters.publish('events', 'run-2', '{"ok":false}');
  assert.deepEqual(instance.getPublished(), [
    { topic: 'events', key: 'run-1', payload: '{"ok":true}' },
    { topic: 'events', key: 'run-2', payload: '{"ok":false}' },
  ]);
});

test('storage write honors idempotency keys and supports reads', async () => {
  const instance = createInmemAdapters();
  await instance.adapters.writeObject('res://kv/users', 'alice', 'v1', 'idem-1');
  await instance.adapters.writeObject('res://kv/users', 'alice', 'v2', 'idem-1');
  const stored = await instance.adapters.readObject('res://kv/users', 'alice');
  assert.equal(stored, 'v1');
  await instance.adapters.writeObject('res://kv/users', 'alice', 'v3');
  const updated = await instance.adapters.readObject('res://kv/users', 'alice');
  assert.equal(updated, 'v3');
});

test('compareAndSwap transitions false to true with matching values', async () => {
  const instance = createInmemAdapters();
  await instance.adapters.writeObject('res://kv/users', 'bob', 'seed');
  const first = await instance.adapters.compareAndSwap('res://kv/users', 'bob', 'other', 'v1');
  assert.equal(first, false);
  const second = await instance.adapters.compareAndSwap('res://kv/users', 'bob', 'seed', 'v2');
  assert.equal(second, true);
  const stored = await instance.adapters.readObject('res://kv/users', 'bob');
  assert.equal(stored, 'v2');
});

test('sign/verify round-trip and hashing return deterministic values', async () => {
  const instance = createInmemAdapters();
  const data = encoder.encode('payload');
  const signature = await instance.adapters.sign('k1', data);
  assert.ok(signature instanceof Uint8Array);
  assert.ok(signature.length > 0);
  const ok = await instance.adapters.verify('k1', data, signature);
  assert.equal(ok, true);
  const digest = await instance.adapters.hash(data);
  assert.match(digest, /^sha256:/);
});

test('hash adapter receives canonicalized bytes from runtime', async () => {
  const instance = createInmemAdapters();
  const runtime = runtimeFromAdapters(instance.adapters);
  const first = await runtime['tf:information/hash@1']({ data: { b: 2, a: 1 } });
  const second = await runtime['tf:information/hash@1']({ data: { a: 1, b: 2 } });
  assert.equal(first.hash, second.hash);
  const permuted = await runtime['tf:information/hash@1']({ data: [{ y: 2, x: 1 }, { x: 1, y: 2 }] });
  const permutedAlt = await runtime['tf:information/hash@1']({ data: [{ x: 1, y: 2 }, { y: 2, x: 1 }] });
  assert.equal(permuted.hash, permutedAlt.hash);
});

test('metrics accumulate counts deterministically', async () => {
  const instance = createInmemAdapters();
  await instance.adapters.emitMetric('pipeline.run');
  await instance.adapters.emitMetric('pipeline.run', 3);
  await instance.adapters.emitMetric('pipeline.error', 0);
  const metrics = instance.getMetrics();
  assert.equal(metrics.get('pipeline.run'), 4);
  assert.equal(metrics.get('pipeline.error'), 0);
});
