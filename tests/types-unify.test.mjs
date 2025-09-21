import { test } from 'node:test';
import assert from 'node:assert/strict';
import {
  any,
  array,
  bytes,
  int,
  object,
  option,
  refined,
  string,
  toJSON,
  unify,
  canonicalStringify
} from '../packages/tf-l0-types/src/types.mjs';

test('unify is commutative and deterministic', () => {
  const digest = refined(string, 'digest_sha256');
  const first = unify(digest, digest);
  const second = unify(digest, digest);
  assert.equal(first.ok, true);
  assert.equal(second.ok, true);
  const keyA = canonicalStringify(toJSON(first.type));
  const keyB = canonicalStringify(toJSON(second.type));
  assert.equal(keyA, keyB);
  const swapped = unify(digest, digest);
  const keySwapped = canonicalStringify(toJSON(swapped.type));
  assert.equal(keyA, keySwapped);
});

test('any unifies with bytes', () => {
  const result = unify(any, bytes);
  assert.equal(result.ok, true);
  assert.equal(canonicalStringify(toJSON(result.type)), canonicalStringify(toJSON(bytes)));
});

test('option(string) unifies with itself', () => {
  const left = option(string);
  const right = option(string);
  const result = unify(left, right);
  assert.equal(result.ok, true);
  assert.equal(canonicalStringify(toJSON(result.type)), canonicalStringify(toJSON(left)));
});

test('bytes and string do not unify', () => {
  const result = unify(bytes, string);
  assert.equal(result.ok, false);
  assert.equal(result.reason, 'kind_mismatch');
});

test('array(string) with array(string) succeeds', () => {
  const result = unify(array(string), array(string));
  assert.equal(result.ok, true);
  const expected = canonicalStringify(toJSON(array(string)));
  assert.equal(canonicalStringify(toJSON(result.type)), expected);
});

test('array(string) with array(int) fails with kind mismatch', () => {
  const mismatch = unify(array(string), array(int));
  assert.equal(mismatch.ok, false);
  assert.equal(mismatch.reason, 'kind_mismatch');
});

test('object shapes require matching required keys', () => {
  const source = object({ key: string, value: string });
  const target = object({ key: string });
  const result = unify(source, target);
  assert.equal(result.ok, false);
  assert.equal(result.reason, 'shape_mismatch');
});

test('object intersection drops optional keys missing on one side', () => {
  const left = object({ a: string, 'b?': array(string) });
  const right = object({ a: string });
  const unified = unify(left, right);
  assert.equal(unified.ok, true);
  const json = toJSON(unified.type);
  assert.deepEqual(json, { object: { a: { string: true } } });
});

test('refinement mismatch is detected', () => {
  const uriString = refined(string, 'uri');
  const plain = string;
  const result = unify(uriString, plain);
  assert.equal(result.ok, false);
  assert.equal(result.reason, 'refinement_mismatch');
});

test('refined uri with refined uri succeeds deterministically', () => {
  const left = refined(string, 'uri');
  const right = refined(string, 'uri');
  const first = unify(left, right);
  const second = unify(left, right);
  assert.equal(first.ok, true);
  assert.equal(second.ok, true);
  assert.equal(canonicalStringify(toJSON(first.type)), canonicalStringify(toJSON(second.type)));
});

