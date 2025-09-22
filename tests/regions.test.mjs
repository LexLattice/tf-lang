// @tf-test kind=product area=runtime speed=fast deps=node
import test from 'node:test';
import assert from 'node:assert/strict';

// Skip if region parser isn't installed
let parse;
try { parse = (await import('../packages/tf-compose/src/parser.with-regions.mjs')).parseDSL; }
catch { test('regions skipped (parser.with-regions.mjs not present)', ()=>{}); process.exit(0); }

const regions = await import('../packages/tf-l0-check/src/regions.mjs');

test('protected ops outside Authorize should be flagged', async () => {
  const src = 'sign-data(key="k1")';
  const ir = parse(src);
  const verdict = regions.checkRegions(ir, {}, ['sign']);
  assert.equal(verdict.ok, false);
});

test('Authorize region satisfies protection', async () => {
  const src = 'authorize{ sign-data(key="k1") }';
  const ir = parse(src);
  const verdict = regions.checkRegions(ir, {}, ['sign']);
  assert.equal(verdict.ok, true);
});
