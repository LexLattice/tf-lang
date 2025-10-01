// @tf-test kind=product area=typechecker speed=fast deps=node

import test from 'node:test';
import assert from 'node:assert/strict';
import { typecheck } from '../typecheck.mjs';

const CSV_ORDER = { schemaRef: 'OrderV1', format: 'csv' };
const JSON_ORDER = { schemaRef: 'OrderV1', format: 'json' };
const AVRO_ORDER = { schemaRef: 'OrderV1', format: 'avro' };

function makeSubscribeNode(varName, type) {
  return {
    id: `S_${varName}`,
    kind: 'Subscribe',
    channel: 'rpc:req:orders',
    qos: 'at_least_once',
    out: { var: varName, type },
    metadata: {
      portTypes: {
        out: {
          [varName]: type,
        },
      },
    },
  };
}

test('typecheck passes when no types are declared', async () => {
  const pipeline = {
    pipeline_id: 'typecheck.none',
    nodes: [
      {
        id: 'S_plain',
        kind: 'Subscribe',
        channel: 'rpc:req:noop',
        qos: 'at_least_once',
        out: { var: 'msg' },
      },
      {
        id: 'T_plain',
        kind: 'Transform',
        spec: { op: 'noop' },
        in: { value: '@msg' },
        out: { var: 'msg2' },
      },
    ],
  };

  const result = await typecheck(pipeline);
  assert.equal(result.status, 'ok');
  assert.equal(result.mismatches.length, 0);
});

test('typecheck suggests adapters when available', async () => {
  const pipeline = {
    pipeline_id: 'typecheck.adapters',
    nodes: [
      makeSubscribeNode('orders_csv', CSV_ORDER),
      {
        id: 'T_require_json',
        kind: 'Transform',
        spec: { op: 'process' },
        in: { value: '@orders_csv' },
        out: { var: 'orders_json' },
        metadata: {
          portTypes: {
            in: {
              value: JSON_ORDER,
            },
            out: {
              orders_json: JSON_ORDER,
            },
          },
        },
      },
      {
        id: 'T_require_avro',
        kind: 'Transform',
        spec: { op: 'persist' },
        in: { value: '@orders_json' },
        out: { var: 'orders_avro' },
        metadata: {
          portTypes: {
            in: {
              value: AVRO_ORDER,
            },
            out: {
              orders_avro: AVRO_ORDER,
            },
          },
        },
      },
    ],
  };

  const result = await typecheck(pipeline);
  assert.equal(result.status, 'needs-adapter');
  assert.equal(result.mismatches.length, 2);
  const [csvToJson, jsonToAvro] = result.mismatches;
  assert.equal(csvToJson.sourceVar, 'orders_csv');
  assert.equal(csvToJson.port, 'in.value');
  assert.deepEqual(csvToJson.portPath, ['value']);
  assert(csvToJson.adapter);
  assert.equal(csvToJson.adapter.op, 'adapter.csv_to_json');
  assert.equal(jsonToAvro.sourceVar, 'orders_json');
  assert.equal(jsonToAvro.port, 'in.value');
  assert(jsonToAvro.adapter);
  assert.equal(jsonToAvro.adapter.op, 'adapter.json_to_avro');
});

test('typecheck fails when no adapter is available', async () => {
  const pipeline = {
    pipeline_id: 'typecheck.missing-adapter',
    nodes: [
      makeSubscribeNode('orders_csv', CSV_ORDER),
      {
        id: 'T_require_unknown',
        kind: 'Transform',
        spec: { op: 'process' },
        in: { value: '@orders_csv' },
        out: { var: 'orders_unknown' },
        metadata: {
          portTypes: {
            in: {
              value: { schemaRef: 'OrderV1', format: 'parquet' },
            },
          },
        },
      },
    ],
  };

  const result = await typecheck(pipeline);
  assert.equal(result.status, 'error');
  assert.equal(result.mismatches.length, 1);
  assert.equal(result.mismatches[0].adapter, null);
  assert.equal(result.mismatches[0].port, 'in.value');
  assert.deepEqual(result.mismatches[0].portPath, ['value']);
});

test('typecheck follows nested port paths and suggests adapters', async () => {
  const pipeline = {
    pipeline_id: 'typecheck.nested-suggestion',
    nodes: [
      makeSubscribeNode('fnol_csv', CSV_ORDER),
      {
        id: 'T_nested',
        kind: 'Transform',
        spec: { op: 'extract' },
        in: {
          payload: {
            claim: '@fnol_csv',
          },
        },
        out: { var: 'claim_json' },
        metadata: {
          port_types: {
            in: {
              payload: {
                claim: JSON_ORDER,
              },
            },
            out: {
              claim_json: JSON_ORDER,
            },
          },
        },
      },
    ],
  };

  const result = await typecheck(pipeline);
  assert.equal(result.status, 'needs-adapter');
  assert.equal(result.mismatches.length, 1);
  const [mismatch] = result.mismatches;
  assert.equal(mismatch.port, 'in.payload.claim');
  assert.deepEqual(mismatch.portPath, ['payload', 'claim']);
  assert.equal(mismatch.sourceVar, 'fnol_csv');
  assert(mismatch.adapter);
  assert.equal(mismatch.adapter.op, 'adapter.csv_to_json');
});

test('typecheck reports nested mismatches without adapters', async () => {
  const pipeline = {
    pipeline_id: 'typecheck.nested-error',
    nodes: [
      makeSubscribeNode('fnol_csv', CSV_ORDER),
      {
        id: 'T_nested_fail',
        kind: 'Transform',
        spec: { op: 'extract' },
        in: {
          payload: {
            claim: '@fnol_csv',
          },
        },
        metadata: {
          port_types: {
            in: {
              payload: {
                claim: { schemaRef: 'FnolV1', format: 'xml' },
              },
            },
          },
        },
      },
    ],
  };

  const result = await typecheck(pipeline);
  assert.equal(result.status, 'error');
  assert.equal(result.mismatches.length, 1);
  const [mismatch] = result.mismatches;
  assert.equal(mismatch.port, 'in.payload.claim');
  assert.deepEqual(mismatch.portPath, ['payload', 'claim']);
  assert.equal(mismatch.adapter, null);
});
