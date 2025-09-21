import test from 'node:test';
import assert from 'node:assert/strict';

import { emitAlloy } from '../packages/tf-l0-proofs/src/alloy.mjs';

function prim(prim, uri) {
  return { node: 'Prim', prim, args: { uri } };
}

test('conflicting writes emit Par and duplicated URIs', () => {
  const ir = {
    node: 'Par',
    children: [prim('write-object', 'res://kv/x'), prim('write-object', 'res://kv/x')]
  };
  const alloy = emitAlloy(ir);
  assert.ok(/one sig Par0 extends Par/.test(alloy), 'includes a Par atom');
  const matches = alloy.match(/uri = "res:\/\/kv\/x"/g) || [];
  assert.equal(matches.length, 2, 'two write bindings with same URI');
  assert.ok(
    /run \{ some p: Par \| Conflicting\[p\] \} for 5/.test(alloy),
    'conflict run command present'
  );
  assert.ok(
    /run \{ all p: Par \| NoConflict\[p\] \} for 5/.test(alloy),
    'no-conflict run command present'
  );
});

test('non-conflicting writes avoid duplicate URIs and are deterministic', () => {
  const ir = {
    node: 'Par',
    children: [prim('write-object', 'res://kv/a'), prim('write-object', 'res://kv/b')]
  };
  const first = emitAlloy(ir);
  const second = emitAlloy(ir);
  assert.equal(first, second, 'emission is deterministic');
  const uriMatches = [...first.matchAll(/uri = "([^"]+)"/g)].map(([, value]) => value);
  const unique = new Set(uriMatches);
  assert.equal(uriMatches.length, unique.size, 'no duplicate URI bindings');
});
