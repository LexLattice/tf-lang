import test from 'node:test';
import assert from 'node:assert/strict';

const parse = (await import('../packages/tf-compose/src/parser.mjs')).parseDSL;
const { canonicalize } = await import('../packages/tf-l0-ir/src/hash.mjs');
const { canon } = await import('../packages/tf-l0-ir/src/normalize.mjs');

const LAWS = {
  idempotent: ['tf:information/hash@1'],
  inverses: [['tf:information/serialize@1', 'tf:information/deserialize@1']],
  commuteWithPure: ['tf:observability/emit-metric@1']
};

function canonIR(src) {
  const ir = parse(src);
  return canon(ir, LAWS);
}

function canonHash(src) {
  const out = canonIR(src);
  return canonicalize(out);
}

const IDENTITY_IR = { node: 'Seq', children: [] };

const identityCanon = canonicalize(canon(IDENTITY_IR, LAWS));

test('idempotent: hash |> hash collapses', () => {
  const h1 = canonHash('hash |> hash');
  const h2 = canonHash('hash');
  assert.equal(h1, h2);
});

test('inverse: serialize |> deserialize eliminates to identity', () => {
  const h1 = canonHash('serialize |> deserialize');
  assert.equal(h1, identityCanon);
});

test('emit-metric commutes with Pure neighbor', () => {
  const a = canonHash('emit-metric(key="ok") |> hash');
  const b = canonHash('hash |> emit-metric(key="ok")');
  assert.equal(a, b);
});
