import test from 'node:test';
import assert from 'node:assert/strict';

import { checkMonotonicLog } from '../../laws/monotonic_log.mjs';

test('monotonic log law records append-only assumption for policy:record channel', () => {
  const nodes = [
    {
      id: 'P_record',
      kind: 'Publish',
      channel: 'policy:record',
      qos: 'at_least_once',
      payload: { record_id: '@recordId', index: '@index' },
    },
    {
      id: 'P_metric',
      kind: 'Publish',
      channel: 'metric:noop',
      qos: 'at_least_once',
      payload: { value: 1 },
    },
  ];

  const report = checkMonotonicLog({ nodes });
  assert.equal(report.ok, true);
  assert.equal(report.results.length, 1);
  const [entry] = report.results;
  assert.equal(entry.id, 'P_record');
  assert.equal(entry.channel, 'policy:record');
  assert.equal(entry.status, 'PASS');
  assert.equal(entry.ok, true);
  assert.equal(entry.reason, null);
  assert.equal(entry.assumption, 'producer-strict-index');
  assert.deepEqual(entry.issues, []);
  assert.equal(entry.indexSource, 'payload.index');
});
