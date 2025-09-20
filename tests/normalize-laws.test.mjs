import test from 'node:test';
import assert from 'node:assert/strict';

const parse = (await import('../packages/tf-compose/src/parser.mjs')).parseDSL;
const { canonicalize } = await import('../packages/tf-l0-ir/src/hash.mjs');
const { canon } = await import('../packages/tf-l0-ir/src/normalize.mjs');

const LAWS = {
  laws: [
    { kind: 'idempotent', applies_to: ['tf:information/hash@1'] },
    { kind: 'inverse', applies_to: ['tf:information/serialize@1', 'tf:information/deserialize@1'] },
    { kind: 'commute-with-pure', applies_to: ['tf:observability/emit-metric@1'] }
  ]
};

function canonHash(src) {
  const ir = parse(src);
  const out = canon(ir, LAWS);
  return canonicalize(out);
}

function identityHash() {
  const identity = { node: 'Seq', children: [] };
  return canonicalize(canon(identity, LAWS));
}

test('idempotent: hash |> hash collapses', () => {
  const h1 = canonHash('hash |> hash');
  const h2 = canonHash('hash');
  assert.equal(h1, h2);
});

test('inverse: serialize |> deserialize eliminates to identity', () => {
  const h1 = canonHash('serialize |> deserialize');
  const h2 = identityHash();
  assert.equal(h1, h2);
});

test('emit-metric commutes with Pure neighbor', () => {
  const a = canonHash('emit-metric(key="ok") |> hash');
  const b = canonHash('hash |> emit-metric(key="ok")');
  assert.equal(a, b);
});
