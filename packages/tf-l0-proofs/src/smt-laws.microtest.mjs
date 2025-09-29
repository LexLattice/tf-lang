import assert from 'node:assert/strict';
import { validateLawEntries } from './smt-laws.mjs';

assert.throws(
  () =>
    validateLawEntries({
      'malformed:test-law': {
        name: 'Malformed test law',
        axioms: ['(assert true)'],
      },
    }),
  (error) => {
    assert.ok(error instanceof Error, 'Expected an Error instance');
    assert.match(error.message, /malformed:test-law/);
    assert.match(error.message, /missing an id/i);
    return true;
  },
  'validateLawEntries should flag entries missing identifiers',
);

console.log('smt-laws validation micro-test passed');
