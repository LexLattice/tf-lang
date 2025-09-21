import test from 'node:test';
import assert from 'node:assert/strict';

const normalizeMod = await import('../packages/tf-l0-ir/src/normalize.mjs');

function prim(id) {
  return { node: 'Prim', prim: id };
}

function seq(children) {
  return { node: 'Seq', children };
}

test('pure nodes stay ahead of observability primitives', () => {
  const identity = prim('tf:core/identity@1');
  const emit = prim('tf:observability/emit-metric@1');
  const expected = seq([prim('tf:core/identity@1'), prim('tf:observability/emit-metric@1')]);

  const alreadyOrdered = seq([identity, emit]);
  assert.deepEqual(normalizeMod.normalize(alreadyOrdered), expected);

  const reversed = seq([emit, identity]);
  assert.deepEqual(normalizeMod.normalize(reversed), expected);
});

test('observability commutes ahead of network out primitives', () => {
  const emit = prim('tf:observability/emit-metric@1');
  const publish = prim('tf:network/publish@1');
  const expected = seq([prim('tf:observability/emit-metric@1'), prim('tf:network/publish@1')]);

  const reversed = seq([publish, emit]);
  assert.deepEqual(normalizeMod.normalize(reversed), expected);
});

test('storage writes block commutation with observability', () => {
  const write = prim('tf:storage/write-object@1');
  const emit = prim('tf:observability/emit-metric@1');
  const input = seq([write, emit]);
  const expected = seq([prim('tf:storage/write-object@1'), prim('tf:observability/emit-metric@1')]);

  assert.deepEqual(normalizeMod.normalize(input), expected);
});

test('region boundaries block commutation across the region', () => {
  const emit = prim('tf:observability/emit-metric@1');
  const publish = prim('tf:network/publish@1');
  const region = {
    node: 'Region',
    kind: 'authorize',
    children: [seq([emit])]
  };
  const input = seq([region, publish]);
  const expectedRegion = {
    node: 'Region',
    kind: 'authorize',
    children: [prim('tf:observability/emit-metric@1')]
  };
  const expected = seq([expectedRegion, prim('tf:network/publish@1')]);

  assert.deepEqual(normalizeMod.normalize(input), expected);
});

test('commutation pass is stable under repeated normalization', () => {
  const emit = prim('tf:observability/emit-metric@1');
  const publish = prim('tf:network/publish@1');
  const identity = prim('tf:core/identity@1');
  const input = seq([publish, emit, identity]);

  const once = normalizeMod.normalize(input);
  const twice = normalizeMod.normalize(once);
  assert.equal(JSON.stringify(once), JSON.stringify(twice));
});
