import assert from 'node:assert/strict';
import { expandPipelineFromYaml } from '../../expander/expand.mjs';

const l2 = `
pipeline: "unit.state"
steps:
  - snap: state.snapshot(entity_id: "acct:123")
  - ver: state.version(entity_id: "acct:123", changeset: { balance: 200, version: 2 })
  - delta: state.diff(left: { balance: 100 }, right: { balance: 120, status: "open" })
  - merge_patch: state.merge(base: { balance: 100 }, patch: [
        { op: "replace", path: "/balance", value: 120 },
        { op: "add", path: "/status", value: "open" }
      ], strategy: "jsonpatch")
  - merge_counter: state.merge(base: { a: 1, b: 4 }, patch: { a: 5, c: 2 }, strategy: "crdt.gcounter")
`;

const dag = expandPipelineFromYaml(l2);

const kernelKinds = new Set(['Keypair', 'Transform', 'Publish', 'Subscribe']);
assert.equal(dag.nodes.every((node) => kernelKinds.has(node.kind)), true, 'only kernel nodes expected');

const byId = Object.fromEntries(dag.nodes.map((node) => [node.id, node]));

const snapPub = byId.P_snap;
assert.equal(snapPub?.channel, 'rpc:req:state/snapshot');
assert.deepEqual(snapPub?.payload?.body, { entity_id: 'acct:123' });
assert.equal(snapPub?.payload?.corr, `@${byId.T_snap_corr.out.var}`);
assert.equal(snapPub?.payload?.reply_to, `@${byId.T_snap_reply_to.out.var}`);
const snapSub = byId.S_snap;
assert.equal(snapSub?.channel, `@${byId.T_snap_reply_to.out.var}`);
assert.equal(snapSub?.filter, `@${byId.T_snap_corr.out.var}`);

const verPub = byId.P_ver;
assert.equal(verPub?.channel, 'rpc:req:state/version');
assert.deepEqual(verPub?.payload?.body, { entity_id: 'acct:123', changeset: { balance: 200, version: 2 } });

const diffNode = byId.T_delta;
assert.equal(diffNode?.spec?.op, 'state_diff');
assert.deepEqual(diffNode?.in, { base: { balance: 100 }, target: { balance: 120, status: 'open' } });

const mergePatch = byId.T_merge_patch;
assert.equal(mergePatch?.spec?.op, 'jsonpatch.apply');
assert.ok(Array.isArray(mergePatch?.notes), 'jsonpatch merge notes should be present');

const mergeCounter = byId.T_merge_counter;
assert.equal(mergeCounter?.spec?.op, 'crdt.gcounter.merge');
assert.ok(Array.isArray(mergeCounter?.laws), 'crdt merge should advertise laws');
assert.deepEqual(
  mergeCounter.laws.map((law) => law.kind).sort(),
  ['associative', 'commutative', 'idempotent']
);

console.log('state macros expansion OK');
