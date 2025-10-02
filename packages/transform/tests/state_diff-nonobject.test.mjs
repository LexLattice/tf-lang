// @tf-test kind=product area=transform speed=fast deps=node

import { test } from 'node:test';
import assert from 'node:assert/strict';
import { runTransform } from '../index.mjs';

const op = { op: 'state_diff' };

test('state_diff reports changed root for differing scalars', () => {
  const diff = runTransform(op, { base: 'left', target: 'right' });
  assert.deepEqual(diff, {
    added: {},
    removed: {},
    changed: {
      '': { from: 'left', to: 'right' },
    },
  });
});

test('state_diff reports changed root for array vs object', () => {
  const diff = runTransform(op, { base: ['a'], target: { 0: 'a' } });
  assert.deepEqual(diff.changed[''], { from: ['a'], to: { 0: 'a' } });
});

test('state_diff returns empty diff when scalars match', () => {
  const diff = runTransform(op, { base: 42, target: 42 });
  assert.deepEqual(diff, { added: {}, removed: {}, changed: {} });
});
