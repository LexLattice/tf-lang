import assert from 'node:assert/strict';
import { expandPipelineFromYaml } from '../../expander/expand.mjs';

const l2 = `
pipeline: "unit.request"
steps:
  - req: interaction.request(endpoint: "api/payments/payout", method: "POST", body: {claim:"X", amount: 100})
`;

const dag = expandPipelineFromYaml(l2);

const byKind = (k) => dag.nodes.filter((n) => n.kind === k);

assert.equal(byKind('Keypair').length >= 1, true, 'Keypair missing');
assert.equal(byKind('Transform').some((n) => n.spec?.op === 'hash' && n.spec?.alg === 'blake3'), true, 'hash(blake3) missing');
assert.equal(byKind('Transform').some((n) => n.spec?.op === 'concat'), true, 'concat reply_to missing');
assert.equal(byKind('Publish').some((n) => String(n.channel).startsWith('rpc:req:')), true, 'Publish rpc:req:* missing');
assert.equal(byKind('Subscribe').length >= 1, true, 'Subscribe reply_to missing');

const transforms = byKind('Transform');
const hashNode = transforms.find((n) => n.spec?.op === 'hash');
assert.ok(hashNode?.in?.k, 'Canonical object lacks key reference');
assert.ok(hashNode?.out?.var, 'Hash node missing corr variable');

const concatNode = transforms.find((n) => n.spec?.op === 'concat');
assert.ok(concatNode?.out?.var, 'Concat node missing reply_to variable');

const corrVar = hashNode.out.var;
const replyVar = concatNode.out.var;

const pub = byKind('Publish').find((n) => String(n.channel).startsWith('rpc:req:'));
assert.ok(pub.payload && 'corr' in pub.payload && 'reply_to' in pub.payload, 'Publish payload lacks corr/reply_to');
assert.equal(pub.payload.corr, `@${corrVar}`, 'Publish corr must match hash output variable');
assert.equal(pub.payload.reply_to, `@${replyVar}`, 'Publish reply_to must match concat output variable');

const sub = byKind('Subscribe')[0];
assert.equal(sub.filter, `@${corrVar}`, 'Subscribe filter must match corr variable');
assert.equal(sub.channel, `@${replyVar}`, 'Subscribe channel must match reply_to variable');

assert.ok(String(dag.effects).includes('Outbound'), 'effects lacks Outbound');
assert.ok(String(dag.effects).includes('Inbound'), 'effects lacks Inbound');

console.log('interaction.request invariants OK');
