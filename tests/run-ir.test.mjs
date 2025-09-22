// @tf-test kind=product area=runtime speed=fast deps=node

import test from 'node:test';
import assert from 'node:assert/strict';

import runIR from '../packages/tf-l0-codegen-ts/src/runtime/run-ir.mjs';
import inmem from '../packages/tf-l0-codegen-ts/src/runtime/inmem.mjs';

test('seq writes produce storage effect and ok', async () => {
  inmem.reset();
  const ir = {
    node: 'Seq',
    children: [
      {
        node: 'Prim',
        prim: 'tf:resource/write-object@1',
        args: { uri: 'res://kv/x', key: 'a', value: 1 },
      },
      {
        node: 'Prim',
        prim: 'tf:resource/write-object@1',
        args: { uri: 'res://kv/x', key: 'b', value: 2 },
      },
    ],
  };
  const { ok, ops, effects } = await runIR(ir, inmem);
  assert.equal(ok, true);
  assert.equal(ops, 2);
  assert.deepEqual(effects, ['Storage.Write']);
});

test('parallel publish and metric capture distinct effects', async () => {
  inmem.reset();
  const ir = {
    node: 'Par',
    children: [
      {
        node: 'Prim',
        prim: 'tf:network/publish@1',
        args: { topic: 't', key: 'k', payload: '{}' },
      },
      {
        node: 'Prim',
        prim: 'tf:observability/emit-metric@1',
        args: { name: 'x' },
      },
    ],
  };
  const out = await runIR(ir, inmem);
  assert.equal(out.ok, true);
  assert.deepEqual(out.effects, ['Network.Out', 'Observability']);
});

test('par run reports ok=false when any child fails', async () => {
  const runtime = {
    'prim:first': async () => ({ ok: true, value: 1 }),
    'prim:second': async () => ({ ok: false, value: 2 }),
  };
  const ir = {
    node: 'Par',
    children: [
      { node: 'Prim', prim: 'prim:first' },
      { node: 'Prim', prim: 'prim:second' },
    ],
  };
  const out = await runIR(ir, runtime);
  assert.equal(out.ok, false);
  assert.deepEqual(out.effects, []);
});

test('seq takes ok from last child', async () => {
  const runtime = {
    'prim:a': async () => ({ ok: false }),
    'prim:b': async () => ({ ok: true }),
  };
  const ir = {
    node: 'Seq',
    children: [
      { node: 'Prim', prim: 'prim:a' },
      { node: 'Prim', prim: 'prim:b' },
    ],
  };
  const out = await runIR(ir, runtime);
  assert.equal(out.ok, true);
});

test('hashing is deterministic for equivalent objects', async () => {
  inmem.reset();
  const hash = inmem['tf:information/hash@1'];
  const { hash: first } = await hash({ value: { b: 2, a: 1 } });
  const { hash: second } = await hash({ value: { a: 1, b: 2 } });
  assert.equal(first, second);
});
