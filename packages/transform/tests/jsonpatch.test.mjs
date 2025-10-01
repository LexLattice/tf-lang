import assert from 'node:assert/strict';
import { runTransform } from '../index.mjs';

const base = { balance: 100 };
const patch = [
  { op: 'add', path: '/temp', value: 'stage' },
  { op: 'replace', path: '/balance', value: 120 },
  { op: 'remove', path: '/temp' }
];

const result = runTransform({ op: 'jsonpatch.apply' }, { base, patch });
assert.deepEqual(result, { balance: 120 });
assert.deepEqual(base, { balance: 100 }, 'base should remain unchanged');

const reversed = runTransform({ op: 'jsonpatch.apply' }, { base, patch: [...patch].reverse() });
assert.deepEqual(reversed, { balance: 120, temp: 'stage' });
assert.notDeepEqual(result, reversed, 'patch application order must matter for jsonpatch');

assert.throws(
  () => runTransform({ op: 'jsonpatch.apply' }, { base, patch: [{ op: 'replace', path: '', value: {} }] }),
  /root operations are not supported/,
  'root replacements must be rejected',
);

assert.throws(
  () => runTransform({ op: 'jsonpatch.apply' }, { base: { list: [] }, patch: [{ op: 'add', path: '/list/0', value: 1 }] }),
  /does not reference an object/,
  'array segments are not supported',
);

assert.throws(
  () => runTransform({ op: 'jsonpatch.apply' }, { base: 5, patch }),
  /base document must be a plain object/,
  'non-object base should fail',
);

console.log('jsonpatch.apply transform OK');
