import test from 'node:test';
import assert from 'node:assert/strict';

import { emitAlloy } from '../packages/tf-l0-proofs/src/alloy.mjs';

test('emits conflicting writes for same URI children', () => {
  const ir = {
    node: 'Authorize',
    children: [
      {
        node: 'Par',
        children: [
          {
            node: 'Prim',
            id: 'write_a',
            writes: [{ uri: 'res://kv/x' }]
          },
          {
            node: 'Prim',
            id: 'write_b',
            writes: [{ uri: 'res://kv/x' }]
          }
        ]
      }
    ]
  };

  const alloy = emitAlloy(ir);
  assert.match(alloy, /one sig Par0 extends Par/, 'should declare Par atom');
  const writeEntries = [...alloy.matchAll(/Write\d+\.uri = "res:\/\/kv\/x"/g)];
  assert.equal(writeEntries.length, 2, 'should emit two writes for same URI');
  assert.ok(
    alloy.includes('run { some p: Par | Conflicting[p] } for 5'),
    'should include conflict run command'
  );
});

test('emits distinct URIs for non-conflicting writes', () => {
  const ir = {
    node: 'Authorize',
    children: [
      {
        node: 'Par',
        children: [
          {
            node: 'Prim',
            id: 'write_a',
            writes: [{ uri: 'res://kv/a' }]
          },
          {
            node: 'Prim',
            id: 'write_b',
            writes: [{ uri: 'res://kv/b' }]
          }
        ]
      }
    ]
  };

  const alloy = emitAlloy(ir);
  const sameUri = alloy.match(/"res:\/\/kv\/a"/g) ?? [];
  assert.equal(sameUri.length, 1, 'only one occurrence of res://kv/a');
  assert.ok(
    alloy.includes('run { all p: Par | NoConflict[p] } for 5'),
    'should include no-conflict run command'
  );
});

test('deterministic emission for identical IR', () => {
  const ir = {
    node: 'Authorize',
    children: [
      {
        node: 'Par',
        children: [
          {
            node: 'Prim',
            id: 'write_a',
            writes: [{ uri: 'res://kv/a' }]
          },
          {
            node: 'Prim',
            id: 'write_b',
            writes: [{ uri: 'res://kv/b' }]
          }
        ]
      }
    ]
  };

  const first = emitAlloy(ir);
  const second = emitAlloy(ir);
  assert.equal(first, second, 'emitter should be deterministic');
});
