// @tf-test kind=product area=expander speed=fast deps=node

import assert from 'node:assert/strict';
import { expandPipelineFromYaml } from '../../expander/expand.mjs';

const l2 = `
pipeline: "unit.process"
steps:
  - req: interaction.request(endpoint: "api/payments/payout", method: "POST", body: { claim: "X", amount: 100 })
  - plan: process.retry(req: "@req", policy: { max_attempts: 3 })
  - any: process.await.any(sources: [
        { channel: "@req.reply_to", filter: "@req.corr" },
        { channel: "@plan.reply_to", filter: "@plan.corr" }
      ])
  - all: process.await.all(sources: [
        { channel: "@req.reply_to", filter: "@req.corr" },
        { channel: "@plan.reply_to", filter: "@plan.corr" }
      ])
  - wait: process.timeout(ms: 5000, reply_to: "@req.reply_to")
  - saga: process.saga(steps: ["reserve", "charge"], compensations: ["cancel", "refund"])
`;

const dag = expandPipelineFromYaml(l2);

const byId = Object.fromEntries(dag.nodes.map((node) => [node.id, node]));

const retryKey = byId.T_plan_retry_key;
assert.equal(retryKey?.spec?.op, 'hash');
assert.equal(retryKey?.in?.target_corr, '@req.corr');

const planPublish = byId.P_plan;
assert.equal(planPublish?.channel, 'rpc:req:retry/plan');
assert.equal(planPublish?.payload?.body?.policy?.max_attempts, 3);
assert.equal(planPublish?.payload?.body?.retry_key, `@${retryKey.out.var}`);
assert.equal(planPublish?.payload?.body?.target_corr, '@req.corr');

const planSubscribe = byId.S_plan;
assert.equal(planSubscribe?.channel, `@${byId.T_plan_reply_to.out.var}`);
assert.equal(planSubscribe?.filter, `@${byId.T_plan_corr.out.var}`);

const anyTransform = byId.T_any;
assert.equal(anyTransform?.spec?.op, 'await.any');
assert.deepEqual(anyTransform?.in?.events, ['@any_0', '@any_1']);
const anySubs = [byId.S_any_0, byId.S_any_1];
assert.equal(anySubs.length, 2);
assert.equal(anySubs[0]?.channel, '@req.reply_to');
assert.equal(anySubs[1]?.channel, '@plan.reply_to');

const allTransform = byId.T_all;
assert.equal(allTransform?.spec?.op, 'await.all');
assert.deepEqual(allTransform?.in?.events, ['@all_0', '@all_1']);

const timeoutPublish = byId.P_wait;
assert.equal(timeoutPublish?.channel, 'rpc:req:scheduler.request');
assert.deepEqual(timeoutPublish?.payload?.body, {
  trigger: { kind: 'timeout', ms: 5000, reply_to: '@req.reply_to' },
});

const sagaTransform = byId.T_saga;
assert.equal(sagaTransform?.spec?.op, 'process.saga.plan');
assert.deepEqual(sagaTransform?.in, {
  steps: ['reserve', 'charge'],
  compensations: ['cancel', 'refund'],
});

console.log('process macros expansion OK');
