/*
 @tf-test
 kind: product
 speed: fast
 deps: node
*/

import test from 'node:test';
import assert from 'node:assert/strict';

import { applyRewritePlan } from '../plan-apply.mjs';
import { analyzePrimitiveSequence, extractPrimitivesFromIr } from '../rewrite-detect.mjs';

function seq(children) {
  return { node: 'Seq', children };
}

function prim(name, extra = {}) {
  return { node: 'Prim', prim: name, ...extra };
}

test('commute obligation swaps emit-metric with pure neighbor', async () => {
  const ir = seq([prim('emit-metric'), prim('hash')]);
  const primitives = extractPrimitivesFromIr(ir);
  const analysis = await analyzePrimitiveSequence(primitives);
  const result = applyRewritePlan(ir, analysis.obligations);
  assert.notEqual(result.ir, ir);
  assert.deepEqual(result.ir.children, [prim('hash'), prim('emit-metric')]);
  assert.deepEqual(result.usedLaws, ['commute:emit-metric-with-pure']);
  assert.equal(result.rewritesApplied, 1);
  assert.deepEqual(ir.children, [prim('emit-metric'), prim('hash')]);
});

test('inverse obligation removes serialize/deserialize pair', async () => {
  const ir = seq([prim('serialize'), prim('deserialize')]);
  const primitives = extractPrimitivesFromIr(ir);
  const analysis = await analyzePrimitiveSequence(primitives);
  const result = applyRewritePlan(ir, analysis.obligations);
  assert.deepEqual(result.ir.children, []);
  assert.deepEqual(result.usedLaws, ['inverse:serialize-deserialize']);
  assert.equal(result.rewritesApplied, 1);
});

test('idempotent obligation drops duplicate hash', async () => {
  const duplicate = prim('hash', { args: { value: 'a' } });
  const ir = seq([duplicate, duplicate]);
  const primitives = extractPrimitivesFromIr(ir);
  const analysis = await analyzePrimitiveSequence(primitives);
  const result = applyRewritePlan(ir, analysis.obligations);
  assert.deepEqual(result.ir.children, [duplicate]);
  assert.deepEqual(result.usedLaws, ['idempotent:hash']);
  assert.equal(result.rewritesApplied, 1);
});

test('applyRewritePlan does not mutate the original IR', async () => {
  const original = seq([
    prim('emit-metric'),
    prim('hash', { args: { value: 'x' } }),
    prim('serialize'),
    prim('deserialize'),
  ]);
  const snapshot = JSON.parse(JSON.stringify(original));
  const primitives = extractPrimitivesFromIr(original);
  const analysis = await analyzePrimitiveSequence(primitives);
  const result = applyRewritePlan(original, analysis.obligations);
  assert.deepEqual(original, snapshot);
  assert.notDeepEqual(result.ir, snapshot);
});
