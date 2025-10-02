// @tf-test kind=product area=checker speed=fast deps=node

import { test } from 'node:test';
import assert from 'node:assert/strict';
import path from 'node:path';
import fsPromises from 'node:fs/promises';
import runChecks, { checkL0 } from '../../packages/checker/check.mjs';

function makePipeline() {
  return {
    pipeline_id: 'checker.test.pipeline',
    effects: 'Outbound+Inbound+Pure',
    nodes: [
      {
        id: 'S_in',
        kind: 'Subscribe',
        channel: 'rpc:req:test/in',
        out: { var: 'incoming' },
      },
      {
        id: 'T_corr',
        kind: 'Transform',
        spec: { op: 'concat' },
        in: { a: '@incoming.corr', b: ':stable' },
        out: { var: 'corr_id' },
      },
      {
        id: 'T_reply',
        kind: 'Transform',
        spec: { op: 'concat' },
        in: { a: 'rpc:reply:', b: '@corr_id' },
        out: { var: 'reply_to' },
      },
      {
        id: 'P_out',
        kind: 'Publish',
        channel: 'rpc:req:test/out',
        payload: {
          corr: '@corr_id',
          body: { message: '@incoming.body' },
          reply_to: '@reply_to',
        },
      },
      {
        id: 'S_reply',
        kind: 'Subscribe',
        channel: '@reply_to',
        filter: '@corr_id',
        out: { var: 'reply_msg' },
      },
    ],
  };
}

test('runChecks reports GREEN for policy-compliant pipeline', async () => {
  const pipeline = makePipeline();
  const report = await runChecks(pipeline, {
    policyPath: path.resolve('policy/policy.allow.json'),
  });

  assert.equal(report.status, 'GREEN');
  assert.equal(report.effects.ok, true);
  assert.equal(report.policy.publish.ok, true);
  assert.equal(report.policy.subscribe.ok, true);
  assert.equal(report.laws.idempotency.ok, true);
  assert.equal(report.laws.crdt_merge.ok, true);
});

test('checkL0 helper loads pipeline from disk', async () => {
  const pipeline = makePipeline();
  const tmpPath = path.resolve('out/test-pipeline.l0.json');
  await fsPromises.mkdir(path.dirname(tmpPath), { recursive: true });
  await fsPromises.writeFile(tmpPath, JSON.stringify(pipeline));

  const report = await checkL0(tmpPath, { policyPath: path.resolve('policy/policy.allow.json') });
  assert.equal(report.status, 'GREEN');
});
