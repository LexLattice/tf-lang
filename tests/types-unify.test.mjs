import test from 'node:test';
import assert from 'node:assert/strict';

const types = await import('../packages/tf-l0-types/src/types.mjs');

const {
  any,
  array,
  bool,
  bytes,
  canonicalJSONStringifyType,
  object,
  option,
  refined,
  string,
  toJSON,
  union,
  unify,
} = types;

test('unify is commutative for arrays', () => {
  const left = array(string());
  const right = array(string());
  const ab = unify(left, right);
  const ba = unify(right, left);
  assert.equal(ab.ok, true);
  assert.equal(ba.ok, true);
  assert.equal(canonicalJSONStringifyType(ab.type), canonicalJSONStringifyType(ba.type));
});

test('unify results are deterministic', () => {
  const left = object({ foo: string(), bar: bool() });
  const right = object({ foo: string(), baz: bool() });
  const first = unify(left, right);
  const second = unify(left, right);
  assert.equal(first.ok, second.ok);
  if (first.ok) {
    assert.equal(canonicalJSONStringifyType(first.type), canonicalJSONStringifyType(second.type));
  } else {
    assert.equal(first.reason, second.reason);
  }
});

test('hash after hash keeps digest refinement', () => {
  const digest = refined(string(), 'digest_sha256');
  const step = unify(digest, any());
  assert.equal(step.ok, true);
  const final = unify(step.type, digest);
  assert.equal(final.ok, true);
  assert.deepEqual(toJSON(final.type), { refined: ['string', 'digest_sha256'] });
});

test('option(string) with option(string) succeeds', () => {
  const left = option(string());
  const right = option(string());
  const result = unify(left, right);
  assert.equal(result.ok, true);
  assert.deepEqual(toJSON(result.type), { option: { string: true } });
});

test('bytes do not unify with string', () => {
  const result = unify(bytes(), string());
  assert.equal(result.ok, false);
  assert.equal(result.reason, 'kind_mismatch');
});

test('object shapes must overlap', () => {
  const left = object({ foo: string() });
  const right = object({ bar: string() });
  const result = unify(left, right);
  assert.equal(result.ok, false);
  assert.equal(result.reason, 'shape_mismatch');
});

test('refinement mismatch is reported', () => {
  const refinedUri = refined(string(), 'uri');
  const plain = string();
  const result = unify(refinedUri, plain);
  assert.equal(result.ok, false);
  assert.equal(result.reason, 'refinement_mismatch');
});

test('union flattening is deterministic', () => {
  const a = union(string(), bool());
  const b = union(bool(), string());
  const result = unify(a, b);
  assert.equal(result.ok, true);
  const expectedMembers = [{ bool: true }, { string: true }];
  assert.deepEqual(toJSON(result.type), { union: expectedMembers });
});
