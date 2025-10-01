// @tf-test kind=product area=checker speed=fast deps=node

import test from 'node:test';
import assert from 'node:assert/strict';
import path from 'node:path';
import fs from 'node:fs/promises';
import runChecks from '../../packages/checker/check.mjs';

const pipeline = {
  pipeline_id: 'capabilities.wildcards',
  effects: 'Outbound+Entropy',
  nodes: [
    {
      id: 'K_identity',
      kind: 'Keypair',
      algorithm: 'Ed25519',
      out: { var: 'kp' },
    },
    {
      id: 'P_reply',
      kind: 'Publish',
      channel: 'rpc:reply:orders',
      qos: 'at_least_once',
      payload: {
        corr: '@kp.public_key_pem',
        reply_to: 'rpc:reply:orders',
      },
    },
  ],
};

const CAPS_DIR = path.resolve('out/tests');

async function writeCapsFile(name, capabilities) {
  await fs.mkdir(CAPS_DIR, { recursive: true });
  const filePath = path.join(CAPS_DIR, name);
  await fs.writeFile(filePath, `${JSON.stringify(capabilities, null, 2)}\n`, 'utf8');
  return filePath;
}

test('wildcard capabilities are required when none are provided', async () => {
  const capsPath = await writeCapsFile('caps-wildcard-empty.json', []);
  const report = await runChecks(pipeline, { capsPath });

  assert.equal(report.status, 'RED');
  assert.equal(report.capabilities.ok, false);
  assert.deepEqual(
    report.capabilities.missing.sort((a, b) => a.localeCompare(b)),
    ['cap:keypair:Ed25519', 'cap:publish:rpc:reply:*']
  );
});

test('wildcard providers satisfy more specific requirements', async () => {
  const capsPath = await writeCapsFile('caps-wildcard-allow.json', [
    'cap:keypair:*',
    'cap:publish:rpc:reply:*',
  ]);
  const report = await runChecks(pipeline, { capsPath });

  assert.equal(report.status, 'GREEN');
  assert.equal(report.capabilities.ok, true);
  assert.deepEqual(report.capabilities.missing, []);
});
