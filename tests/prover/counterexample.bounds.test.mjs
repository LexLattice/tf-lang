// @tf-test kind=proofs area=prover speed=fast deps=node

import test from 'node:test';
import assert from 'node:assert/strict';

import { findCounterexample } from '../../packages/prover/counterexample.mjs';

test('counterexample search returns structured payload when max bools exceeded', () => {
  const result = findCounterexample({
    goal: 'branch-exclusive',
    guard: '@decision',
    variables: ['a', 'b', 'c', 'd', 'e', 'f', 'g', 'h', 'i'],
    predicate: () => true,
    positive: [],
    negative: [],
    maxBools: 9,
  });

  assert.equal(result.reason, 'max-bools-exceeded');
  assert.deepEqual(result.assignment, {});
  assert.deepEqual(result.triggered, { positive: [], negative: [] });
});

test('counterexample search returns sorted assignment keys and triggered sets', () => {
  const result = findCounterexample({
    goal: 'branch-exclusive',
    guard: '@decision',
    variables: ['b', 'a'],
    predicate: (candidate) => candidate.a,
    positive: [
      { id: 'P_b', guard: { kind: 'var', var: 'b', negated: false } },
    ],
    negative: [
      { id: 'N_a', guard: { kind: 'var', var: 'a', negated: true } },
    ],
    maxBools: 2,
  });

  assert.equal(result.reason, 'overlap');
  assert.deepEqual(Object.keys(result.assignment), ['a', 'b']);
  assert.deepEqual(result.triggered.positive, []);
  assert.deepEqual(result.triggered.negative, ['N_a']);
});
