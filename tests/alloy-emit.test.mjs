// @tf-test kind=proofs area=alloy speed=fast deps=node

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

function makeSeq(children) {
  return { node: 'Seq', children };
}

function extractRunLines(alloy) {
  return alloy
    .split('\n')
    .filter((line) => line.startsWith('run {'))
    .map((line) => line.trim());
}

test('conflict model emits nested writes with identical uri', () => {
  const ir = {
    node: 'Par',
    children: [
      makeSeq([makePrim('res://kv/x')]),
      makeSeq([makePrim('res://kv/x')])
    ]
  };

  const alloy = emitAlloy(ir);
  assert.match(alloy, /open util\/strings/, 'should open util/strings module');
  assert.match(
    alloy,
    /a\.node in p\.\*children && b\.node in p\.\*children/,
    'should use transitive closure for conflict detection'
  );

  const uriMatches = alloy.match(/Writes\d+\.uri = "res:\/\/kv\/x"/g) || [];
  assert.equal(uriMatches.length, 2, 'expected two writes targeting the same URI');

  const runLines = extractRunLines(alloy);
  assert.equal(runLines.length, 2, 'expected two run commands');
  for (const line of runLines) {
    assert.ok(!/ for \d+$/.test(line), 'run commands should omit scope when not provided');
  }
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

test('scope option appends bound to run commands', () => {
  const ir = {
    node: 'Par',
    children: [makePrim('res://kv/a'), makePrim('res://kv/b')]
  };

  const alloy = emitAlloy(ir, { scope: 12 });
  const runLines = extractRunLines(alloy);
  assert.equal(runLines.length, 2, 'expected two run commands');
  for (const line of runLines) {
    assert.ok(line.endsWith(' for 12'), 'run command should include the provided scope');
  }
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
