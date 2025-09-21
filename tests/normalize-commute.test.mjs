import test from 'node:test';
import assert from 'node:assert/strict';

const { normalize } = await import('../packages/tf-l0-ir/src/normalize.mjs');

function prim(id) {
  return { node: 'Prim', prim: id };
}

function seq(children) {
  return { node: 'Seq', children };
}

test('Pure stays ordered before Observability', () => {
  const input = seq([
    prim('tf:pure/identity@1'),
    prim('tf:observability/emit-metric@1')
  ]);
  const output = normalize(input);
  assert.deepEqual(output, input);
});

test('Observability bubbles ahead of Pure neighbor', () => {
  const input = seq([
    prim('tf:observability/emit-metric@1'),
    prim('tf:pure/identity@1')
  ]);
  const expected = seq([
    prim('tf:pure/identity@1'),
    prim('tf:observability/emit-metric@1')
  ]);
  const output = normalize(input);
  assert.deepEqual(output, expected);
});

test('Network.Out settles after Observability when commuting', () => {
  const forward = seq([
    prim('tf:observability/emit-metric@1'),
    prim('tf:network/publish@1')
  ]);
  const reverse = seq([
    prim('tf:network/publish@1'),
    prim('tf:observability/emit-metric@1')
  ]);
  const expected = normalize(forward);
  assert.deepEqual(expected, seq([
    prim('tf:observability/emit-metric@1'),
    prim('tf:network/publish@1')
  ]));
  const reordered = normalize(reverse);
  assert.deepEqual(reordered, expected);
});

test('Storage.Write remains a barrier for reordering', () => {
  const input = seq([
    prim('tf:storage/write-object@1'),
    prim('tf:observability/emit-metric@1')
  ]);
  const output = normalize(input);
  assert.deepEqual(output, input);
});

test('Region boundary prevents commuting across', () => {
  const input = {
    node: 'Seq',
    children: [
      {
        node: 'Region',
        children: [prim('tf:observability/emit-metric@1')]
      },
      prim('tf:network/publish@1')
    ]
  };
  const output = normalize(input);
  assert.deepEqual(output, input);
});

test('Normalization is stable under repeated application', () => {
  const input = seq([
    prim('tf:network/publish@1'),
    prim('tf:observability/emit-metric@1'),
    prim('tf:pure/identity@1')
  ]);
  const once = normalize(input);
  const twice = normalize(once);
  assert.deepEqual(once, twice);
  assert.equal(JSON.stringify(once), JSON.stringify(twice));
});
