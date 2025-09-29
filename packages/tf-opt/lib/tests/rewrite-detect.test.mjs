import test from 'node:test';
import assert from 'node:assert/strict';
import { analyzePrimitiveSequence } from '../rewrite-detect.mjs';

const COMMUTE_LAW = 'commute:emit-metric-with-pure';

test('hash followed by emit-metric counts as a rewrite', async () => {
  const result = await analyzePrimitiveSequence(['hash', 'emit-metric']);
  assert.equal(result.rewritesApplied, 1);
  assert.deepEqual(result.laws, [COMMUTE_LAW]);
});

test('emit-metric followed by hash is also counted', async () => {
  const result = await analyzePrimitiveSequence(['emit-metric', 'hash']);
  assert.equal(result.rewritesApplied, 1);
  assert.deepEqual(result.laws, [COMMUTE_LAW]);
});
