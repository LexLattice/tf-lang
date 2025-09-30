import { test } from 'node:test';
import assert from 'node:assert/strict';
import { hashPayload } from '../../packages/runtime/run.mjs';

test('blake3 digest is stable across key ordering', () => {
  const first = { a: 1, b: { c: 2, d: 3 } };
  const second = { b: { d: 3, c: 2 }, a: 1 };

  const hashA = hashPayload(first, { alg: 'blake3' });
  const hashB = hashPayload(second, { alg: 'blake3' });

  assert.equal(hashA, hashB);
});
