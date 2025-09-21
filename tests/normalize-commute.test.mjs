import test from 'node:test';
import assert from 'node:assert/strict';

import { normalize } from '../packages/tf-l0-ir/src/normalize.mjs';
import { canonicalize } from '../packages/tf-l0-ir/src/hash.mjs';

const PURE = 'tf:information/hash@1';
const OBS = 'tf:observability/emit-metric@1';
const NET = 'tf:network/publish@1';
const WRITE = 'tf:storage/write-object@1';

function makePrim(prim) {
  return { node: 'Prim', prim };
}

function makeSeq(children) {
  return { node: 'Seq', children };
}

function primOrder(node) {
  if (!node || node.node !== 'Seq') {
    return [];
  }
  return (node.children ?? [])
    .filter((child) => child?.node === 'Prim')
    .map((child) => child.prim);
}

test('Pure and Observability remain in canonical order', () => {
  const ordered = makeSeq([makePrim(PURE), makePrim(OBS)]);
  const normalizedOrdered = normalize(ordered);
  assert.deepEqual(primOrder(normalizedOrdered), [PURE, OBS]);

  const reversed = makeSeq([makePrim(OBS), makePrim(PURE)]);
  const normalizedReversed = normalize(reversed);
  assert.deepEqual(primOrder(normalizedReversed), [PURE, OBS]);
});

test('Observability bubbles left of Network.Out when commuting', () => {
  const reversed = makeSeq([makePrim(NET), makePrim(OBS)]);
  const normalized = normalize(reversed);
  assert.deepEqual(primOrder(normalized), [OBS, NET]);
});

test('Storage.Write remains a barrier for Observability', () => {
  const seq = makeSeq([makePrim(WRITE), makePrim(OBS)]);
  const normalized = normalize(seq);
  assert.deepEqual(primOrder(normalized), [WRITE, OBS]);
});

test('Region boundaries prevent commuting across the region', () => {
  const region = { node: 'Region', children: [makePrim(OBS)] };
  const seq = makeSeq([region, makePrim(NET)]);
  const normalized = normalize(seq);

  assert.equal(normalized.node, 'Seq');
  const children = normalized.children ?? [];
  assert.equal(children.length, 2);
  assert.equal(children[0].node, 'Region');
  assert.equal(children[1].node, 'Prim');
  assert.equal(children[1].prim, NET);
  const regionChildren = children[0].children ?? [];
  assert.equal(regionChildren.length, 1);
  assert.equal(regionChildren[0].prim, OBS);
});

test('Normalization with commutation is a fixpoint', () => {
  const seq = makeSeq([
    makePrim(NET),
    makePrim(OBS),
    makePrim(PURE),
    makePrim(NET),
    makePrim(OBS)
  ]);
  const first = normalize(seq);
  const second = normalize(first);
  assert.equal(canonicalize(first), canonicalize(second));
});
