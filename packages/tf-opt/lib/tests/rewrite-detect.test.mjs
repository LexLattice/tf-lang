// @tf-test kind: product speed: fast deps: node

import test from 'node:test';
import assert from 'node:assert/strict';
import { analyzePrimitiveSequence } from '../rewrite-detect.mjs';

const COMMUTE_LAW = 'commute:emit-metric-with-pure';
const INVERSE_LAW = 'inverse:serialize-deserialize';
const IDEMPOTENT_LAW = 'idempotent:hash';

function assertSingleLaw(result, expectedLaw) {
  assert.equal(result.obligations.length, 1);
  assert.equal(result.rewritesApplied, 1);
  assert.deepEqual(result.laws, [expectedLaw]);
  assert.equal(result.obligations[0].law, expectedLaw);
}

test('hash followed by emit-metric does not create a commute obligation (normalized to left)', async () => {
  const result = await analyzePrimitiveSequence(['hash', 'emit-metric']);
  assert.deepEqual(result.primitives, ['hash', 'emit-metric']);
  assert.equal(result.rewritesApplied, 0);
  assert.deepEqual(result.laws, []);
});

test('emit-metric followed by hash counts as commute (left case)', async () => {
  const result = await analyzePrimitiveSequence(['emit-metric', 'hash']);
  assert.deepEqual(result.primitives, ['emit-metric', 'hash']);
  assertSingleLaw(result, COMMUTE_LAW);
});

test('serialize followed by deserialize is inverse', async () => {
  const result = await analyzePrimitiveSequence(['serialize', 'deserialize']);
  assertSingleLaw(result, INVERSE_LAW);
});

test('duplicate hash is idempotent', async () => {
  const result = await analyzePrimitiveSequence(['hash', 'hash']);
  assertSingleLaw(result, IDEMPOTENT_LAW);
});
