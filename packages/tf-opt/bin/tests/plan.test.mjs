// @tf-test kind: product speed: fast deps: node

import test from 'node:test';
import assert from 'node:assert/strict';
import { buildPlan } from '../opt.mjs';

const COMMUTE_LAW = 'commute:emit-metric-with-pure';
const INVERSE_LAW = 'inverse:serialize-deserialize';
const IDEMPOTENT_LAW = 'idempotent:hash';

test('buildPlan merges analysis and IR metadata deterministically', () => {
  const analysis = {
    laws: [INVERSE_LAW],
    obligations: [
      { law: COMMUTE_LAW, rewrite: 'swap-hash-emit' },
      { law: COMMUTE_LAW, rewrite: 'swap-hash-emit' },
    ],
    rewrites: [
      { law: IDEMPOTENT_LAW, rewrite: 'dedupe-hash' },
    ],
    rewritesApplied: 2,
  };

  const ir = {
    meta: {
      optimizer: {
        used_laws: [IDEMPOTENT_LAW, '   '],
        rewrites: [
          { law: INVERSE_LAW, rewrite: 'normalize-io' },
          { law: COMMUTE_LAW, rewrite: 'swap-hash-emit' },
        ],
        rewrites_applied: 5,
      },
    },
  };

  const plan = buildPlan(ir, analysis);
  assert.deepEqual(plan, {
    rewrites_applied: 5,
    used_laws: [COMMUTE_LAW, IDEMPOTENT_LAW, INVERSE_LAW],
    rewrites: [
      { law: IDEMPOTENT_LAW, rewrite: 'dedupe-hash' },
      { law: INVERSE_LAW, rewrite: 'normalize-io' },
      { law: COMMUTE_LAW, rewrite: 'swap-hash-emit' },
    ],
  });
});

test('buildPlan throws on unknown laws gathered from IR', () => {
  const ir = {
    meta: {
      optimizer: {
        used_laws: ['unknown:law'],
      },
    },
  };

  assert.throws(
    () => buildPlan(ir, {}),
    /unknown law\(s\): unknown:law/,
  );
});
