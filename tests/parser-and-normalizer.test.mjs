// @tf-test kind=product area=parser speed=fast deps=node
import test from 'node:test';
import assert from 'node:assert/strict';

// Import project files dynamically relative to repo structure
const parse = await import('../packages/tf-compose/src/parser.mjs').catch(()=>import('../packages/tf-compose/src/parser.with-regions.mjs'));
const irHash = await import('../packages/tf-l0-ir/src/hash.mjs');
const normalize = await import('../packages/tf-l0-ir/src/normalize.mjs');

test('normalize is idempotent', async () => {
  const src = 'hash |> hash';
  const ir = parse.parseDSL(src);
  const n1 = normalize.normalize(ir, { laws: [{ kind:'idempotent', applies_to:['tf:information/hash@1'] }] });
  const n2 = normalize.normalize(n1, { laws: [{ kind:'idempotent', applies_to:['tf:information/hash@1'] }] });
  assert.equal(irHash.canonicalize(n1), irHash.canonicalize(n2));
});

test('par conflict example should be a Par node', async () => {
  const src = 'par{ write-object(uri="res://kv/b", key="x"); write-object(uri="res://kv/b", key="x") }';
  const ir = parse.parseDSL(src);
  assert.equal(ir.node, 'Par');
});
