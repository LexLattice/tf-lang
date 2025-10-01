import assert from 'node:assert/strict';
import { expandPipelineFromYaml } from '../../expander/expand.mjs';

const l2 = `
pipeline: "unit.policy"
steps:
  - enforce: policy.enforce(policy: { name: "fraud-check" }, input: { actor: "acct:1", amount: 250 })
`;

const dag = expandPipelineFromYaml(l2);

const kernelKinds = new Set(['Keypair', 'Transform', 'Publish', 'Subscribe']);
assert.equal(dag.nodes.every((node) => kernelKinds.has(node.kind)), true, 'only kernel nodes expected');

const byId = Object.fromEntries(dag.nodes.map((node) => [node.id, node]));

const evalNode = byId.T_enforce;
assert.equal(evalNode?.spec?.op, 'policy_eval');
assert.equal(evalNode?.out?.var, 'enf_enforce');

const publishNode = byId.P_enforce;
assert.equal(publishNode?.channel, 'policy:enforce');
assert.equal(publishNode?.payload?.decision, '@enf_enforce');
assert.deepEqual(publishNode?.payload?.inputs, { actor: 'acct:1', amount: 250 });

console.log('policy.enforce macro expansion OK');
