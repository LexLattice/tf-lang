import assert from 'node:assert/strict';
import { expandPipelineFromYaml } from '../../expander/expand.mjs';

const l2 = `
pipeline: "unit.schedule"
steps:
  - sched: process.schedule(task_ref: "auto.claim", trigger: { kind: "cron", expr: "0 * * * *" })
`;

const dag = expandPipelineFromYaml(l2);

const byKind = (k) => dag.nodes.filter((n) => n.kind === k);

assert.equal(byKind('Keypair').length >= 1, true, 'Keypair missing');
assert.equal(byKind('Transform').some((n) => n.spec?.op === 'hash' && n.spec?.alg === 'blake3'), true, 'hash(blake3) missing');
assert.equal(byKind('Transform').some((n) => n.spec?.op === 'concat'), true, 'concat reply_to missing');

const transforms = byKind('Transform');
const hashNode = transforms.find((n) => n.spec?.op === 'hash');
const concatNode = transforms.find((n) => n.spec?.op === 'concat');
assert.ok(hashNode?.out?.var, 'Hash node missing corr variable');
assert.ok(concatNode?.out?.var, 'Concat node missing reply_to variable');

const corrVar = hashNode.out.var;
const replyVar = concatNode.out.var;

const pub = byKind('Publish').find((n) => n.channel === 'rpc:req:scheduler.request');
assert.ok(pub, 'Publish rpc:req:scheduler.request missing');
assert.equal(pub.payload?.corr, `@${corrVar}`, 'Publish corr must match hash output variable');
assert.equal(pub.payload?.reply_to, `@${replyVar}`, 'Publish reply_to must match concat output variable');
assert.deepEqual(pub.payload?.body, { task_ref: 'auto.claim', trigger: { kind: 'cron', expr: '0 * * * *' } });
assert.equal(pub.payload?.method, 'POST');

const sub = byKind('Subscribe')[0];
assert.ok(sub, 'Subscribe reply_to missing');
assert.equal(sub.channel, `@${replyVar}`, 'Subscribe channel must match reply_to variable');
assert.equal(sub.filter, `@${corrVar}`, 'Subscribe filter must match corr variable');

console.log('process.schedule invariants OK');
