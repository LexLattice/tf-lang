// @tf-test kind=product area=transform speed=fast deps=node

import { test } from 'node:test';
import assert from 'node:assert/strict';
import { runTransform } from '../index.mjs';

const op = { op: 'state_diff' };

test('state_diff detects added, removed, and changed keys', () => {
  const base = { a: 1, b: 2 };
  const target = { b: 3, c: 4 };
  const diff = runTransform(op, { base, target });
  assert.deepEqual(diff.added, { c: 4 });
  assert.deepEqual(diff.removed, { a: 1 });
  assert.deepEqual(diff.changed, { b: { from: 2, to: 3 } });
});

test('state_diff recurses through nested objects', () => {
  const base = { meta: { flags: { send: false }, version: 1 } };
  const target = { meta: { flags: { send: true }, version: 2 } };
  const diff = runTransform(op, { base, target });
  assert.deepEqual(diff.added, {});
  assert.deepEqual(diff.removed, {});
  assert.ok('meta' in diff.changed);
  assert.deepEqual(diff.changed.meta.added, {});
  assert.deepEqual(diff.changed.meta.removed, {});
  assert.deepEqual(diff.changed.meta.changed.version, { from: 1, to: 2 });
  assert.deepEqual(diff.changed.meta.changed.flags.changed.send, { from: false, to: true });
});

test('state_diff is deterministic', () => {
  const base = { items: ['a', 'b'] };
  const target = { items: ['a', 'c'] };
  const first = runTransform(op, { base, target });
  const second = runTransform(op, { base, target });
  assert.deepEqual(first, second);
});
