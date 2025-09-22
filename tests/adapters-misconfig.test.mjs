// @tf-test kind=product area=adapters speed=fast deps=node

import test from 'node:test';
import assert from 'node:assert/strict';

import runIR from '../packages/tf-l0-codegen-ts/src/runtime/run-ir.mjs';
import { createInmemRuntime } from '../packages/tf-l0-codegen-ts/src/runtime/inmem.mjs';
import { createInmemAdapters } from '../packages/tf-l0-codegen-ts/src/adapters/inmem.mjs';

function runtimeWith(modifier) {
  const adapters = createInmemAdapters({ keys: { k1: 'secret' } });
  if (typeof modifier === 'function') {
    modifier(adapters);
  }
  return createInmemRuntime({ adapters });
}

test('write-object fails fast when adapter is missing', async () => {
  const runtime = runtimeWith((adapters) => {
    delete adapters.writeObject;
  });
  const ir = {
    node: 'Prim',
    prim: 'tf:resource/write-object@1',
    args: { uri: 'res://kv/users', key: 'alice', value: { status: 'new' } },
  };
  await assert.rejects(() => runIR(ir, runtime), /adapter missing: writeObject/);
});

test('publish and emit-metric require adapter implementations', async () => {
  const publishRuntime = runtimeWith((adapters) => {
    delete adapters.publish;
  });
  const publishIR = {
    node: 'Prim',
    prim: 'tf:network/publish@1',
    args: { topic: 'orders', key: 'ord-1', payload: { status: 'new' } },
  };
  await assert.rejects(() => runIR(publishIR, publishRuntime), /adapter missing: publish/);

  const metricRuntime = runtimeWith((adapters) => {
    delete adapters.emitMetric;
  });
  const metricIR = {
    node: 'Prim',
    prim: 'tf:observability/emit-metric@1',
    args: { name: 'flows.processed', value: 1 },
  };
  await assert.rejects(() => runIR(metricIR, metricRuntime), /adapter missing: emitMetric/);
});

test('verify primitive fails fast when adapter missing or signature mismatches', async () => {
  const missingVerifyRuntime = runtimeWith((adapters) => {
    delete adapters.verify;
  });
  const verifyIR = {
    node: 'Prim',
    prim: 'tf:security/verify-signature@1',
    args: { key: 'k1', payload: 'payload', signature: 'sig' },
  };
  await assert.rejects(() => runIR(verifyIR, missingVerifyRuntime), /adapter missing: verify/);

  const failingVerifyRuntime = runtimeWith((adapters) => {
    adapters.verify = async () => false;
  });
  await assert.rejects(() => runIR(verifyIR, failingVerifyRuntime), /signature verification failed/);
});

test('hash primitive requires adapter implementation', async () => {
  const runtime = runtimeWith((adapters) => {
    delete adapters.hash;
  });
  const hashIR = {
    node: 'Prim',
    prim: 'tf:information/hash@1',
    args: { value: { a: 1 } },
  };
  await assert.rejects(() => runIR(hashIR, runtime), /adapter missing: hash/);
});

test('capability guard rejects denied Storage.Write operations', async () => {
  const runtime = createInmemRuntime();
  const ir = {
    node: 'Prim',
    prim: 'tf:resource/write-object@1',
    args: { uri: 'res://kv/private', key: 'alice', value: 'secret' },
  };
  const caps = { effects: ['Network.Out'], allow_writes_prefixes: [] };
  await assert.rejects(() => runIR(ir, runtime, { caps }), /capability denied: Storage.Write/);
});
