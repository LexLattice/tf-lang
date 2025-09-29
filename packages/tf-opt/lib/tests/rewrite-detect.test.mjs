import test from 'node:test';
import assert from 'node:assert/strict';
import { analyzePrimitiveSequence } from '../rewrite-detect.mjs';

const COMMUTE_LAW = 'commute:emit-metric-with-pure';
const INVERSE_LAW = 'inverse:serialize-deserialize';
const IDEMPOTENT_LAW = 'idempotent:hash';

test('emit-metric followed by hash registers commute obligation', async () => {
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

test('serialize followed by deserialize is an inverse obligation', async () => {
  const result = await analyzePrimitiveSequence(['serialize', 'deserialize']);
  assert.equal(result.obligations.length, 1);
  assert.equal(result.rewritesApplied, 1);
  assert.deepEqual(result.laws, [INVERSE_LAW]);
  assert.deepEqual(result.obligations[0], {
    law: INVERSE_LAW,
    span: [0, 1],
    primitives: ['serialize', 'deserialize'],
  });
});

test('duplicate hash primitives are idempotent obligations', async () => {
  const duplicate = { name: 'hash', node: { node: 'Prim', prim: 'hash' } };
  const result = await analyzePrimitiveSequence([duplicate, duplicate]);
  assert.equal(result.obligations.length, 1);
  assert.equal(result.rewritesApplied, 1);
  assert.deepEqual(result.laws, [IDEMPOTENT_LAW]);
  assert.deepEqual(result.obligations[0], {
    law: IDEMPOTENT_LAW,
    span: [0, 1],
    primitives: ['hash', 'hash'],
  });
});
