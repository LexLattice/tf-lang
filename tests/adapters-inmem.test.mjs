import test from 'node:test';
import assert from 'node:assert/strict';

import { createInmemAdapters } from '../packages/tf-l0-codegen-ts/src/adapters/inmem.mjs';

function bytesOf(text) {
  return Uint8Array.from(Buffer.from(text, 'utf8'));
}

test('publish entries accumulate', async () => {
  const adapters = createInmemAdapters();
  await adapters.publish('events', 'k1', '{"a":1}');
  await adapters.publish('events', 'k2', '{"a":2}');
  const published = adapters.getPublished();
  assert.equal(published.length, 2);
  assert.deepEqual(published[0], { topic: 'events', key: 'k1', payload: '{"a":1}' });
});

test('idempotent writeObject honors idempotencyKey', async () => {
  const adapters = createInmemAdapters();
  await adapters.writeObject('res://kv/demo', 'doc', 'first', 'ik-1');
  await adapters.writeObject('res://kv/demo', 'doc', 'second', 'ik-1');
  const stored = await adapters.readObject('res://kv/demo', 'doc');
  assert.equal(stored, 'first');
});

test('compareAndSwap requires matching expected value', async () => {
  const adapters = createInmemAdapters();
  await adapters.writeObject('res://kv/demo', 'flag', 'off');
  const fail = await adapters.compareAndSwap('res://kv/demo', 'flag', 'on', 'mid');
  assert.equal(fail, false);
  const ok = await adapters.compareAndSwap('res://kv/demo', 'flag', 'off', 'on');
  assert.equal(ok, true);
  const stored = await adapters.readObject('res://kv/demo', 'flag');
  assert.equal(stored, 'on');
});

test('sign and verify succeed for matching inputs', async () => {
  const adapters = createInmemAdapters({ keys: { k1: 'secret-key' } });
  const payload = bytesOf('payload');
  const signature = await adapters.sign('k1', payload);
  const ok = await adapters.verify('k1', payload, signature);
  assert.equal(ok, true);
  const bad = await adapters.verify('k1', payload, Uint8Array.from(signature, (b) => b ^ 0xff));
  assert.equal(bad, false);
});

test('emitMetric aggregates counts deterministically', async () => {
  const adapters = createInmemAdapters();
  await adapters.emitMetric('jobs');
  await adapters.emitMetric('jobs', 2);
  await adapters.emitMetric('errors');
  const metrics = adapters.getMetrics();
  assert.equal(metrics.get('jobs'), 3);
  assert.equal(metrics.get('errors'), 1);
});
