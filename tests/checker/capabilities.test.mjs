// @tf-test kind=product area=checker speed=fast deps=node

import { test } from 'node:test';
import assert from 'node:assert/strict';
import path from 'node:path';
import fs from 'node:fs/promises';
import runChecks from '../../packages/checker/check.mjs';

test('checker reports missing capabilities when not provided', async () => {
  const pipeline = {
    pipeline_id: 'capabilities.test',
    effects: 'Entropy',
    nodes: [
      {
        id: 'K',
        kind: 'Keypair',
        algorithm: 'Ed25519',
        out: { var: 'kp' },
      },
    ],
  };

  const capsPath = path.resolve('out/empty-caps.json');
  await fs.mkdir(path.dirname(capsPath), { recursive: true });
  await fs.writeFile(capsPath, '[]\n');

  const report = await runChecks(pipeline, {
    policyPath: path.resolve('policy/policy.allow.json'),
    capsPath,
  });

  assert.equal(report.capabilities.ok, false);
  assert.deepEqual(report.capabilities.missing, ['cap:keypair:Ed25519']);
  assert.equal(report.status, 'RED');
});
