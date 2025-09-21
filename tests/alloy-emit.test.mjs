import test from 'node:test';
import assert from 'node:assert/strict';

import { emitAlloy } from '../packages/tf-l0-proofs/src/alloy.mjs';

const duplicateUri = 'res://kv/x';
const uniqueUri = 'res://kv/y';

const conflictIR = {
  node: 'Region',
  children: [
    {
      node: 'Par',
      children: [
        {
          node: 'Prim',
          prim: 'write-object',
          writes: [{ uri: duplicateUri }],
        },
        {
          node: 'Prim',
          prim: 'write-object',
          writes: [{ uri: duplicateUri }],
        },
      ],
    },
  ],
};

const okIR = {
  node: 'Region',
  children: [
    {
      node: 'Par',
      children: [
        {
          node: 'Prim',
          prim: 'write-object',
          writes: [{ uri: duplicateUri }],
        },
        {
          node: 'Prim',
          prim: 'write-object',
          writes: [{ uri: uniqueUri }],
        },
      ],
    },
  ],
};

test('conflict IR emits duplicate write URIs', () => {
  const alloy = emitAlloy(conflictIR);
  assert.ok(/one sig Par0 extends Par/.test(alloy), 'Par atom should be declared');
  const uris = collectWriteUris(alloy);
  assert.equal(uris.filter((uri) => uri === duplicateUri).length, 2, 'two identical writes');
  assert.ok(
    alloy.includes('run { some p: Par | Conflicting[p] } for 5'),
    'conflict run command present'
  );
});

test('ok IR has no duplicate write URIs', () => {
  const alloy = emitAlloy(okIR);
  const uris = collectWriteUris(alloy);
  const duplicates = new Set();
  for (const uri of uris) {
    if (duplicates.has(uri)) {
      assert.fail(`duplicate URI detected: ${uri}`);
    }
    duplicates.add(uri);
  }
  assert.ok(
    alloy.includes('run { some p: Par | Conflicting[p] } for 5'),
    'commands are present for completeness'
  );
});

test('emission is deterministic', () => {
  const first = emitAlloy(okIR);
  const second = emitAlloy(okIR);
  assert.equal(first, second);
});

function collectWriteUris(alloy) {
  const matches = alloy.matchAll(/\.uri = "([^"]*)"/g);
  const uris = [];
  for (const match of matches) {
    uris.push(match[1]);
  }
  return uris;
}
