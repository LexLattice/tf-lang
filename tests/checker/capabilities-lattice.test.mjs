// @tf-test kind=product area=checker speed=fast deps=node

import test from 'node:test';
import assert from 'node:assert/strict';
import path from 'node:path';
import fs from 'node:fs/promises';
import runChecks from '../../packages/checker/check.mjs';

const pipeline = {
  pipeline_id: 'capabilities.lattice',
  effects: 'Outbound+Inbound+Entropy',
  nodes: [
    {
      id: 'S_req',
      kind: 'Subscribe',
      channel: 'rpc:req:orders',
      qos: 'at_least_once',
      out: { var: 'request' },
    },
    {
      id: 'K_reply',
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
        body: {
          status: 'ok',
          original: '@request.body',
        },
      },
    },
  ],
};

function sortStrings(values) {
  return [...values].map(String).sort((a, b) => a.localeCompare(b));
}

test('capability lattice marks missing capabilities when none provided', async () => {
  const emptyCapsPath = path.resolve('out/tests/caps-empty.json');
  await fs.mkdir(path.dirname(emptyCapsPath), { recursive: true });
  await fs.writeFile(emptyCapsPath, '[]\n', 'utf8');

  const report = await runChecks(pipeline, { capsPath: emptyCapsPath });

  assert.equal(report.status, 'RED');
  assert.equal(report.capabilities.ok, false);
  assert.deepEqual(
    sortStrings(report.capabilities.required),
    ['cap:keypair:Ed25519', 'cap:publish:rpc:reply:*', 'cap:subscribe:rpc:req:*']
  );
  assert.deepEqual(
    sortStrings(report.capabilities.missing),
    ['cap:keypair:Ed25519', 'cap:publish:rpc:reply:*', 'cap:subscribe:rpc:req:*']
  );
});

test('capability lattice turns report green when capabilities are provided', async () => {
  const allowCapsPath = path.resolve('out/tests/caps-allow.json');
  await fs.mkdir(path.dirname(allowCapsPath), { recursive: true });
  await fs.writeFile(
    allowCapsPath,
    JSON.stringify(
      ['cap:keypair:Ed25519', 'cap:publish:rpc:reply:*', 'cap:subscribe:rpc:req:*'],
      null,
      2
    ),
    'utf8'
  );

  const report = await runChecks(pipeline, { capsPath: allowCapsPath });

  assert.equal(report.status, 'GREEN');
  assert.equal(report.capabilities.ok, true);
  assert.deepEqual(
    sortStrings(report.capabilities.required),
    ['cap:keypair:Ed25519', 'cap:publish:rpc:reply:*', 'cap:subscribe:rpc:req:*']
  );
  assert.deepEqual(report.capabilities.missing, []);
});
