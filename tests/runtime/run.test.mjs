import { test } from 'node:test';
import assert from 'node:assert/strict';
import executeL0 from '../../packages/runtime/run.mjs';

test('executeL0 runs subscribe -> transform -> publish pipeline', async () => {
  const l0 = {
    pipeline_id: 'test.pipeline',
    nodes: [
      {
        id: 'S_in',
        kind: 'Subscribe',
        channel: 'rpc:req:test/input',
        out: { var: 'incoming' },
      },
      {
        id: 'T_corr',
        kind: 'Transform',
        spec: { op: 'concat' },
        in: { a: '@incoming.msg', b: '-stable' },
        out: { var: 'corr_id' },
      },
      {
        id: 'P_out',
        kind: 'Publish',
        channel: 'rpc:req:test/output',
        payload: {
          corr: '@corr_id',
          body: { value: '@incoming.msg' },
        },
      },
    ],
  };

  const result = await executeL0(l0, {
    seed: [
      {
        topic: 'rpc:req:test/input',
        message: { corr: 'seed', msg: 'hello' },
      },
    ],
  });

  assert.equal(result.context.corr_id, 'hello-stable');
  assert.equal(result.trace.publishes.length, 1);
  assert.equal(result.trace.publishes[0].channel, 'rpc:req:test/output');
  assert.equal(result.trace.publishes[0].payload.body.value, 'hello');
});
