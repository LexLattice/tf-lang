import test from 'node:test';
import assert from 'node:assert/strict';
import {
  any,
  array,
  bytes,
  object as objectType,
  option,
  refined,
  string as stringType,
  toJSON,
  unify
} from '../packages/tf-l0-types/src/types.mjs';

test('unify is commutative and deterministic for successes', () => {
  const scenarios = [
    [refined(stringType(), 'digest_sha256'), any()],
    [option(stringType()), option(stringType())]
  ];
  for (const [left, right] of scenarios) {
    const first = unify(left, right);
    assert.equal(first.ok, true);
    const swapped = unify(right, left);
    assert.equal(swapped.ok, true);
    assert.deepEqual(
      JSON.stringify(toJSON(first.type)),
      JSON.stringify(toJSON(swapped.type)),
      'commutative result mismatch'
    );
    const repeat = unify(left, right);
    assert.equal(JSON.stringify(toJSON(first.type)), JSON.stringify(toJSON(repeat.type)), 'non-deterministic result');
  }
});

test('hash output unifies with hash input via any', () => {
  const hashed = refined(stringType(), 'digest_sha256');
  const result = unify(hashed, any());
  assert.equal(result.ok, true);
  assert.deepEqual(toJSON(result.type), toJSON(hashed));
  const chained = unify(result.type, hashed);
  assert.equal(chained.ok, true);
  assert.deepEqual(toJSON(chained.type), toJSON(hashed));
});

test('option(string) unifies with option(string)', () => {
  const left = option(stringType());
  const right = option(stringType());
  const verdict = unify(left, right);
  assert.equal(verdict.ok, true);
  assert.deepEqual(toJSON(verdict.type), toJSON(option(stringType())));
});

test('bytes and string do not unify', () => {
  const verdict = unify(bytes(), stringType());
  assert.equal(verdict.ok, false);
  assert.equal(verdict.reason, 'kind_mismatch');
  const swapped = unify(stringType(), bytes());
  assert.equal(swapped.ok, false);
  assert.equal(swapped.reason, 'kind_mismatch');
});

test('object shape mismatch is reported', () => {
  const a = objectType({ topic: stringType(), key: stringType() });
  const b = objectType({ topic: stringType() });
  const verdict = unify(a, b);
  assert.equal(verdict.ok, false);
  assert.equal(verdict.reason, 'shape_mismatch');
});

test('refinement mismatch is reported', () => {
  const refinedUri = refined(stringType(), 'uri');
  const plain = stringType();
  const verdict = unify(refinedUri, plain);
  assert.equal(verdict.ok, false);
  assert.equal(verdict.reason, 'refinement_mismatch');
  const swapped = unify(plain, refinedUri);
  assert.equal(swapped.ok, false);
  assert.equal(swapped.reason, 'refinement_mismatch');
});

test('array element mismatches propagate reasons', () => {
  const left = array(bytes());
  const right = array(stringType());
  const verdict = unify(left, right);
  assert.equal(verdict.ok, false);
  assert.equal(verdict.reason, 'kind_mismatch');
});
