// @tf-test kind=product area=adapters speed=fast deps=node

import test from 'node:test';
import assert from 'node:assert/strict';

import { createInmemAdapters } from '../packages/tf-l0-codegen-ts/src/adapters/inmem.mjs';

const encoder = new TextEncoder();

function snapshotStorage(adapters) {
  const state = adapters.getStorageSnapshot?.();
  return state ?? {};
}

test('publish records entries in insertion order', async () => {
  const adapters = createInmemAdapters();
  await adapters.publish('orders', 'o-1', '{"qty":1}');
  await adapters.publish('orders', 'o-2', '{"qty":2}');

  const published = adapters.getPublished();
  assert.equal(published.length, 2);
  assert.deepEqual(published[0], { topic: 'orders', key: 'o-1', payload: '{"qty":1}' });
  assert.deepEqual(published[1], { topic: 'orders', key: 'o-2', payload: '{"qty":2}' });

  adapters.reset();
  assert.equal(adapters.getPublished().length, 0);
});

test('writeObject honours idempotency key', async () => {
  const adapters = createInmemAdapters();
  const uri = 'res://kv/users';
  const key = 'alice';

  await adapters.writeObject(uri, key, 'pending', 'token-1');
  await adapters.writeObject(uri, key, 'active', 'token-1');

  const stored = snapshotStorage(adapters);
  assert.equal(stored[uri][key], 'pending');

  const readBack = await adapters.readObject(uri, key);
  assert.equal(readBack, 'pending');
});

test('compareAndSwap transitions only on expected value', async () => {
  const adapters = createInmemAdapters();
  const uri = 'res://kv/users';
  const key = 'bob';

  await adapters.writeObject(uri, key, 'pending');
  const miss = await adapters.compareAndSwap(uri, key, 'archived', 'active');
  assert.equal(miss, false);
  assert.equal(snapshotStorage(adapters)[uri][key], 'pending');

  const hit = await adapters.compareAndSwap(uri, key, 'pending', 'active');
  assert.equal(hit, true);
  assert.equal(snapshotStorage(adapters)[uri][key], 'active');
});

test('sign and verify round trip with deterministic output', async () => {
  const adapters = createInmemAdapters({ keys: { k1: 'secret' } });
  const payload = encoder.encode('hello world');

  const signature = await adapters.sign('k1', payload);
  assert.ok(signature instanceof Uint8Array);

  const verified = await adapters.verify('k1', payload, signature);
  assert.equal(verified, true);

  const tampered = await adapters.verify('k1', encoder.encode('tampered'), signature);
  assert.equal(tampered, false);
});

test('emitMetric accumulates counters and exposes totals', async () => {
  const adapters = createInmemAdapters();
  await adapters.emitMetric('flows.processed');
  await adapters.emitMetric('flows.processed', 3);
  await adapters.emitMetric('flows.failed', 2);

  const totals = adapters.getMetricTotals();
  assert.deepEqual(totals, { 'flows.processed': 4, 'flows.failed': 2 });
});

test('hash produces sha256 hex digest of bytes', async () => {
  const adapters = createInmemAdapters();
  const digest = await adapters.hash(encoder.encode('hash me'));
  assert.match(digest, /^[0-9a-f]{64}$/);
});
