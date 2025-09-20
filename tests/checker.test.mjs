import test from 'node:test';
import assert from 'node:assert/strict';
const parse = await import('../packages/tf-compose/src/parser.mjs').catch(()=>import('../packages/tf-compose/src/parser.with-regions.mjs'));
const check = await import('../packages/tf-l0-check/src/check.mjs');
const cat = await import('node:fs/promises').then(fs => fs.readFile('packages/tf-l0-spec/spec/catalog.json','utf8').then(JSON.parse).catch(()=>({primitives:[]})));

test('Par write conflict should fail', async () => {
  const src = 'par{ write-object(uri="res://kv/bucket", key="x", value="1"); write-object(uri="res://kv/bucket", key="x", value="2") }';
  const ir = parse.parseDSL(src);
  const verdict = check.checkIR(ir, cat);
  assert.equal(verdict.ok, false);
});
