import test from 'node:test';
import assert from 'node:assert/strict';

import checkBranchExclusive from '../../laws/branch_exclusive.mjs';

function buildNodes({ elseGuard }) {
  return [
    {
      id: 'P_then',
      kind: 'Publish',
      channel: 'metric:then',
      qos: 'at_least_once',
      payload: { value: 1 },
      when: '@decision',
      metadata: { branch: { id: 'decision_branch', path: 'then' } },
    },
    {
      id: 'P_else',
      kind: 'Publish',
      channel: 'metric:else',
      qos: 'at_least_once',
      payload: { value: 1 },
      when: elseGuard,
      metadata: { branch: { id: 'decision_branch', path: 'else' } },
    },
  ];
}

test('branch exclusivity succeeds when guards are complementary', async () => {
  const nodes = buildNodes({ elseGuard: { op: 'not', var: 'decision' } });
  const report = await checkBranchExclusive({ nodes });

  assert.equal(report.ok, true);
  assert.equal(report.results.length, 1);
  const [entry] = report.results;
  assert.equal(entry.status, 'PASS');
  assert.equal(entry.reason, null);
  assert.equal(entry.ok, true);
  assert.equal(entry.proved, true);
  assert.equal(entry.guardVar, 'decision');
  assert.equal(entry.guard, '@decision');
});

test('branch exclusivity detects non-exclusive guards', async () => {
  const nodes = buildNodes({ elseGuard: '@decision' });
  const report = await checkBranchExclusive({ nodes });

  assert.equal(report.ok, false);
  const [entry] = report.results;
  assert.equal(entry.status, 'ERROR');
  assert.equal(entry.reason, 'overlap');
  assert.equal(entry.proved, false);
  assert.equal(entry.ok, false);
});
