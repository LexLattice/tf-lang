import test from 'node:test';
import assert from 'node:assert/strict';

const { normalize } = await import('../packages/tf-l0-ir/src/normalize.mjs');
const { canonicalize } = await import('../packages/tf-l0-ir/src/hash.mjs');

const catalog = {
  primitives: [
    { id: 'tf:pure/hash@1', name: 'hash', effects: ['Pure'] },
    { id: 'tf:observability/emit-metric@1', name: 'emit-metric', effects: ['Observability'] },
    { id: 'tf:network/publish@1', name: 'publish', effects: ['Network.Out'] },
    { id: 'tf:storage/write-object@1', name: 'write-object', effects: ['Storage.Write'] }
  ]
};

function prim(primId) {
  return { node: 'Prim', prim: primId, args: {} };
}

function seq(children) {
  return { node: 'Seq', children };
}

test('pure and observability stay in canonical order', () => {
  const input = seq([prim('tf:pure/hash@1'), prim('tf:observability/emit-metric@1')]);
  const normalized = normalize(input, {}, { catalog });
  assert.deepEqual(normalized, seq([
    prim('tf:pure/hash@1'),
    prim('tf:observability/emit-metric@1')
  ]));
});

test('pure bubbles left of observability when reversed', () => {
  const input = seq([prim('tf:observability/emit-metric@1'), prim('tf:pure/hash@1')]);
  const expected = seq([
    prim('tf:pure/hash@1'),
    prim('tf:observability/emit-metric@1')
  ]);
  const normalized = normalize(input, {}, { catalog });
  assert.deepEqual(normalized, expected);
});

test('observability moves ahead of Network.Out when they commute', () => {
  const input = seq([prim('tf:network/publish@1'), prim('tf:observability/emit-metric@1')]);
  const normalized = normalize(input, {}, { catalog });
  assert.deepEqual(normalized, seq([
    prim('tf:observability/emit-metric@1'),
    prim('tf:network/publish@1')
  ]));
});

test('storage writes block commutation', () => {
  const input = seq([prim('tf:storage/write-object@1'), prim('tf:observability/emit-metric@1')]);
  const normalized = normalize(input, {}, { catalog });
  const expected = seq([
    prim('tf:storage/write-object@1'),
    prim('tf:observability/emit-metric@1')
  ]);
  assert.deepEqual(normalized, expected);
});

test('region boundaries prevent cross-region swaps', () => {
  const region = { node: 'Region', kind: 'authorize', children: [prim('tf:observability/emit-metric@1')] };
  const input = seq([region, prim('tf:network/publish@1')]);
  const normalized = normalize(input, {}, { catalog });
  const expected = seq([
    { node: 'Region', kind: 'authorize', children: [prim('tf:observability/emit-metric@1')] },
    prim('tf:network/publish@1')
  ]);
  assert.deepEqual(normalized, expected);
});

test('normalization is stable under repeated application', () => {
  const input = seq([
    prim('tf:network/publish@1'),
    prim('tf:pure/hash@1'),
    prim('tf:observability/emit-metric@1')
  ]);
  const once = normalize(input, {}, { catalog });
  const twice = normalize(JSON.parse(JSON.stringify(once)), {}, { catalog });
  assert.equal(canonicalize(once), canonicalize(twice));
});
