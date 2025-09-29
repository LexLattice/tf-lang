import test from 'node:test';
import assert from 'node:assert/strict';
import { analyzePrimitiveSequence } from '../rewrite-detect.mjs';

const COMMUTE_LAW = 'commute:emit-metric-with-pure';

function assertSingleCommute(result) {
  assert.equal(result.rewritesApplied, 1);
  assert.equal(result.obligations.length, 1);
  assert.deepEqual(result.laws, [COMMUTE_LAW]);
  assert.deepEqual(result.obligations[0], {
    law: COMMUTE_LAW,
    span: [0, 1],
    primitives: ['hash', 'emit-metric'],
  });
}

test('hash followed by emit-metric counts as a rewrite', async () => {
  const result = await analyzePrimitiveSequence(['hash', 'emit-metric']);
  assert.deepEqual(result.primitives, ['hash', 'emit-metric']);
  assertSingleCommute(result);
});

test('emit-metric followed by hash is also counted', async () => {
  const result = await analyzePrimitiveSequence(['emit-metric', 'hash']);
  assert.deepEqual(result.primitives, ['emit-metric', 'hash']);
  assert.equal(result.rewritesApplied, 1);
  assert.equal(result.obligations.length, 1);
  assert.deepEqual(result.laws, [COMMUTE_LAW]);
  assert.deepEqual(result.obligations[0], {
    law: COMMUTE_LAW,
    span: [0, 1],
    primitives: ['emit-metric', 'hash'],
  });
});
