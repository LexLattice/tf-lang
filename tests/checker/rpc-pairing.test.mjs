import { test } from 'node:test';
import assert from 'node:assert/strict';
import runChecks from '../../packages/checker/check.mjs';

test('rpc publish has paired subscribe filtered by corr', async () => {
  const l0 = {
    pipeline_id: 'rpc.pairing.test',
    effects: 'Outbound+Inbound+Entropy+Pure',
    nodes: [
      { id: 'K', kind: 'Keypair', algorithm: 'Ed25519', out: { var: 'kp' } },
      {
        id: 'Tcorr',
        kind: 'Transform',
        spec: { op: 'hash', alg: 'blake3' },
        in: { k: '@kp.public_key_pem', e: 'api/x', m: 'POST' },
        out: { var: 'corr' },
      },
      {
        id: 'Treply',
        kind: 'Transform',
        spec: { op: 'concat' },
        in: { a: 'rpc:reply:', b: '@corr' },
        out: { var: 'reply' },
      },
      {
        id: 'P',
        kind: 'Publish',
        channel: 'rpc:req:api/x',
        payload: { method: 'POST', corr: '@corr', reply_to: '@reply' },
      },
      {
        id: 'S',
        kind: 'Subscribe',
        channel: '@reply',
        filter: '@corr',
        out: { var: 'response' },
      },
    ],
  };
  const report = await runChecks(l0, { policyPath: 'policy/policy.allow.json' });
  assert.equal(report.laws.rpc_pairing.ok, true);
  const pairing = report.laws.rpc_pairing.results.find((entry) => entry.id === 'P');
  assert.ok(pairing, 'expected pairing entry for publish P');
  assert.equal(pairing.hasReplySub, true);
  assert.equal(pairing.filterMatchesCorr, true);
  const idempotency = report.laws.idempotency.results.find((entry) => entry.id === 'P');
  assert.ok(idempotency, 'expected idempotency entry for publish P');
  assert.equal(idempotency.entropyRooted, true);
  assert.equal(report.status, 'GREEN');
});
