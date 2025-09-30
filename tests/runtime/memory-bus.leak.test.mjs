import { test } from 'node:test';
import assert from 'node:assert/strict';
import createMemoryBus from '../../packages/runtime/bus.memory.mjs';

test('delivered messages are removed when not retained', async () => {
  const bus = createMemoryBus({ defaultTimeout: 20 });
  const pending = bus.receive('rpc:req:leak', { timeout: 50 });
  await bus.publish('rpc:req:leak', { corr: 'leak-test' });
  const entry = await pending;
  assert.equal(entry.message.corr, 'leak-test');
  const snapshot = bus.snapshot('rpc:req:leak');
  assert.deepEqual(snapshot, []);
});
