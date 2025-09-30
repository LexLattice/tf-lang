import { test } from 'node:test';
import assert from 'node:assert/strict';
import createMemoryBus from '../../packages/runtime/bus.memory.mjs';

test('memory bus delivers duplicates with at-least-once semantics', async () => {
  const bus = createMemoryBus({ defaultTimeout: 20 });
  await bus.publish('rpc:req:test', { corr: 'dup-1' }, { duplicates: 2 });

  const first = await bus.receive('rpc:req:test', { timeout: 20 });
  const second = await bus.receive('rpc:req:test', { timeout: 20 });
  const third = await bus.receive('rpc:req:test', { timeout: 20 });

  assert.equal(first.meta.attempt, 1);
  assert.equal(second.meta.attempt, 2);
  assert.equal(third.meta.attempt, 3);
  assert.equal(second.meta.duplicate, true);
  assert.equal(third.meta.duplicate, true);
});

test('memory bus filters by corr values', async () => {
  const bus = createMemoryBus({ defaultTimeout: 20 });
  const wait = bus.receive('rpc:req:test', { filter: 'corr:other', timeout: 10 });
  await bus.publish('rpc:req:test', { corr: 'corr:expected', payload: { corr: 'corr:expected' } });
  await assert.rejects(wait, /timeout/);

  const match = await bus.receive('rpc:req:test', { filter: 'corr:expected', timeout: 20 });
  assert.equal(match.message.corr, 'corr:expected');
});
