// @tf-test kind=product area=checker speed=fast deps=node

import test from 'node:test';
import assert from 'node:assert/strict';

import checkBranchExclusive from '../../laws/branch_exclusive.mjs';

test('branch exclusivity normalizes guard strings and objects', async () => {
  const nodes = [
    {
      id: 'P_then',
      kind: 'Publish',
      channel: 'metric:then',
      when: '@decision',
      metadata: { branch: { id: 'decision', path: 'then' } },
    },
    {
      id: 'P_else',
      kind: 'Publish',
      channel: 'metric:else',
      when: '!( @decision )',
      metadata: { branch: { id: 'decision', path: 'else' } },
    },
    {
      id: 'P_else_object',
      kind: 'Publish',
      channel: 'metric:else',
      when: { op: 'not', var: '@decision' },
      metadata: { branch: { id: 'decision', path: 'else' } },
    },
  ];

  const report = await checkBranchExclusive({ nodes });
  assert.equal(report.ok, true);
  const [entry] = report.results;
  assert.equal(entry.status, 'PASS');
  assert.equal(entry.guardVar, 'decision');
  assert.equal(entry.guard, '@decision');
  assert.equal(entry.ok, true);
  assert.equal(entry.proved, true);
});

test('metadata polarity mismatches surface as warnings', async () => {
  const nodes = [
    {
      id: 'P_then',
      kind: 'Publish',
      channel: 'metric:then',
      when: 'not @decision',
      metadata: { branch: { id: 'decision', path: 'then' } },
    },
    {
      id: 'P_else',
      kind: 'Publish',
      channel: 'metric:else',
      when: '@decision',
      metadata: { branch: { id: 'decision', path: 'else' } },
    },
  ];

  const report = await checkBranchExclusive({ nodes });
  assert.equal(report.ok, true);
  const [entry] = report.results;
  assert.equal(entry.status, 'WARN');
  assert.equal(entry.reason, 'metadata-guard-mismatch');
  assert.equal(entry.ok, true);
  assert.equal(entry.proved, true);
  assert.equal(entry.guard, '@decision');
});
