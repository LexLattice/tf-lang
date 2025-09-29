// @tf-test kind: product speed: fast deps: node

import test from 'node:test';
import assert from 'node:assert/strict';
import {
  stableStringify,
  normalizeRewriteEntries,
  buildUsedLawManifest,
} from '../utils.mjs';

const COMMUTE_LAW = 'commute:emit-metric-with-pure';
const INVERSE_LAW = 'inverse:serialize-deserialize';
const IDEMPOTENT_LAW = 'idempotent:hash';

test('stableStringify sorts object keys recursively', () => {
  const input = {
    beta: 1,
    alpha: {
      zeta: 3,
      gamma: 2,
    },
  };
  const expected = [
    '{',
    '  "alpha": {',
    '    "gamma": 2,',
    '    "zeta": 3',
    '  },',
    '  "beta": 1',
    '}',
  ].join('\n');
  assert.equal(stableStringify(input), expected);
});

test('stableStringify respects explicit key ordering priorities', () => {
  const input = {
    gamma: { beta: 2, alpha: 1 },
    beta: 1,
    alpha: 0,
  };
  const expected = [
    '{',
    '  "beta": 1,',
    '  "alpha": 0,',
    '  "gamma": {',
    '    "alpha": 1,',
    '    "beta": 2',
    '  }',
    '}',
  ].join('\n');
  assert.equal(
    stableStringify(input, { keyOrder: { '': ['beta', 'alpha'], gamma: ['alpha', 'beta'] } }),
    expected,
  );
});

test('normalizeRewriteEntries dedupes and sorts by rewrite then law', () => {
  const entries = [
    { law: COMMUTE_LAW, rewrite: 'swap-hash-emit' },
    { law: INVERSE_LAW, rewrite: 'normalize-io' },
    { law: COMMUTE_LAW, rewrite: 'swap-hash-emit' },
    { law: IDEMPOTENT_LAW, rewrite: 'dedupe-hash' },
    { law: INVERSE_LAW, rewrite: 'normalize-io' },
    { law: COMMUTE_LAW, rewrite: 'adjust-primitives' },
  ];
  assert.deepEqual(normalizeRewriteEntries(entries), [
    { law: COMMUTE_LAW, rewrite: 'adjust-primitives' },
    { law: IDEMPOTENT_LAW, rewrite: 'dedupe-hash' },
    { law: INVERSE_LAW, rewrite: 'normalize-io' },
    { law: COMMUTE_LAW, rewrite: 'swap-hash-emit' },
  ]);
});

test('buildUsedLawManifest merges plan data and extras deterministically', () => {
  const initialPlan = {
    used_laws: [INVERSE_LAW, COMMUTE_LAW],
    rewrites: [
      { law: COMMUTE_LAW, rewrite: 'swap-hash-emit' },
      { law: INVERSE_LAW, rewrite: 'normalize-io' },
    ],
  };
  const planOnly = buildUsedLawManifest({ plans: [initialPlan] });
  assert.deepEqual(planOnly, {
    used_laws: [COMMUTE_LAW, INVERSE_LAW],
    rewrites: [
      { law: INVERSE_LAW, rewrite: 'normalize-io' },
      { law: COMMUTE_LAW, rewrite: 'swap-hash-emit' },
    ],
  });

  const postPlan = {
    used_laws: [IDEMPOTENT_LAW],
    rewrites: [
      { law: IDEMPOTENT_LAW, rewrite: 'dedupe-hash' },
      { law: COMMUTE_LAW, rewrite: 'swap-hash-emit' },
    ],
  };
  const manifest = buildUsedLawManifest({
    plans: [initialPlan, postPlan],
    extras: [[IDEMPOTENT_LAW], new Set([COMMUTE_LAW])],
  });
  assert.deepEqual(manifest, {
    used_laws: [COMMUTE_LAW, IDEMPOTENT_LAW, INVERSE_LAW],
    rewrites: [
      { law: IDEMPOTENT_LAW, rewrite: 'dedupe-hash' },
      { law: INVERSE_LAW, rewrite: 'normalize-io' },
      { law: COMMUTE_LAW, rewrite: 'swap-hash-emit' },
    ],
  });
});
