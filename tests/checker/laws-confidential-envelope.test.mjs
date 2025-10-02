// @tf-test kind=product area=checker speed=fast deps=node

import test from 'node:test';
import assert from 'node:assert/strict';

import { checkConfidentialEnvelope } from '../../laws/confidential_envelope.mjs';

test('confidential envelope law marks payloads without plaintext as pass and warns otherwise', () => {
  const nodes = [
    {
      id: 'P_secure',
      kind: 'Publish',
      channel: 'policy:secure',
      qos: 'at_least_once',
      payload: {
        envelope: { ciphertext: 'ABC123' },
      },
    },
    {
      id: 'P_warn',
      kind: 'Publish',
      channel: 'policy:secure',
      qos: 'at_least_once',
      payload: {
        envelope: { ciphertext: 'XYZ' },
        plaintext: { hint: true },
      },
    },
  ];

  const report = checkConfidentialEnvelope({ nodes });
  assert.equal(report.ok, true);
  assert.equal(report.results.length, 2);

  const secure = report.results.find((entry) => entry.id === 'P_secure');
  assert(secure);
  assert.equal(secure.status, 'PASS');
  assert.equal(secure.reason, null);
  assert.equal(secure.satisfied, true);
  assert.equal(secure.ok, true);

  const warn = report.results.find((entry) => entry.id === 'P_warn');
  assert(warn);
  assert.equal(warn.status, 'WARN');
  assert.equal(warn.reason, 'plaintext-present');
  assert.equal(warn.satisfied, false);
  assert.equal(warn.ok, true);
});
