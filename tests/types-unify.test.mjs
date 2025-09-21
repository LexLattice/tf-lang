import { test } from 'node:test';
import assert from 'node:assert/strict';
import {
  any,
  array,
  bytes,
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

test('object shapes require matching required keys', () => {
  const source = object({ key: string, value: string });
  const target = object({ key: string });
  const result = unify(source, target);
  assert.equal(result.ok, false);
  assert.equal(result.reason, 'shape_mismatch');
});

test('refinement mismatch is detected', () => {
  const uriString = refined(string, 'uri');
  const plain = string;
  const result = unify(uriString, plain);
  assert.equal(result.ok, false);
  assert.equal(result.reason, 'refinement_mismatch');
});

test('arrays unify element-wise', () => {
  const left = array(refined(string, 'symbol'));
  const right = array(refined(string, 'symbol'));
  const result = unify(left, right);
  assert.equal(result.ok, true);
  assert.equal(canonicalStringify(toJSON(result.type)), canonicalStringify(toJSON(left)));
});

