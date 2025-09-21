import test from 'node:test';
import assert from 'node:assert/strict';

import { emitAlloy } from '../packages/tf-l0-proofs/src/alloy.mjs';

function makePrim(uri, overrides = {}) {
  return {
    node: 'Prim',
    prim: 'write-object',
    writes: uri ? [{ uri }] : [],
    args: uri ? { uri } : {},
    ...overrides
  };
}

test('conflict model emits writes with identical uri', () => {
  const ir = {
    node: 'Par',
    children: [makePrim('res://kv/x'), makePrim('res://kv/x')]
  };

  const alloy = emitAlloy(ir);
  assert.match(alloy, /one sig Par0 extends Par/, 'should declare a Par atom');
  const uriMatches = alloy.match(/Writes\d+\.uri = "res:\/\/kv\/x"/g) || [];
  assert.equal(uriMatches.length, 2, 'expected two writes targeting the same URI');
  assert.ok(alloy.includes('run { some p: Par | Conflicting[p] } for 5'));
  assert.ok(alloy.includes('run { all p: Par | NoConflict[p] } for 5'));
});

test('non-conflict model omits duplicate uri writes', () => {
  const ir = {
    node: 'Par',
    children: [makePrim('res://kv/a'), makePrim('res://kv/b')]
  };

  const alloy = emitAlloy(ir);
  const uriMatches = [...alloy.matchAll(/Writes\d+\.uri = "([^"]+)"/g)];
  const uris = uriMatches.map((match) => match[1]);
  const unique = new Set(uris);
  assert.equal(unique.size, uris.length, 'writes should not reuse the same URI');
});

test('emission is deterministic', () => {
  const ir = {
    node: 'Par',
    children: [makePrim('res://kv/a'), makePrim('res://kv/b')]
  };

  const first = emitAlloy(ir);
  const second = emitAlloy(ir);
  assert.equal(first, second);
});
