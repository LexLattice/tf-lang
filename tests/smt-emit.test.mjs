import test from 'node:test';
import assert from 'node:assert/strict';
import { readFile } from 'node:fs/promises';

const parse = await import('../packages/tf-compose/src/parser.mjs').catch(() => import('../packages/tf-compose/src/parser.with-regions.mjs'));
const { emitSMT } = await import('../packages/tf-l0-proofs/src/smt.mjs');

async function loadIR(flowPath) {
  const src = await readFile(flowPath, 'utf8');
  return parse.parseDSL(src);
}

function findFirstPar(node) {
  if (!node || typeof node !== 'object') {
    return null;
  }
  if (node.node === 'Par') {
    return node;
  }
  if (Array.isArray(node.children)) {
    for (const child of node.children) {
      const res = findFirstPar(child);
      if (res) return res;
    }
  }
  return null;
}

test('storage_conflict emits conflict booleans', async () => {
  const ir = await loadIR('examples/flows/storage_conflict.tf');
  const smt = emitSMT(ir);
  assert.match(smt, /\(assert \(not \(or conflict_/);
  const conflictDecls = smt.match(/\(declare-const conflict_[^\s]+ Bool\)/g) || [];
  assert.ok(conflictDecls.length >= 1);
});

test('storage_ok encoding is deterministic and sized by children', async () => {
  const ir = await loadIR('examples/flows/storage_ok.tf');
  const parNode = findFirstPar(ir);
  const childCount = Array.isArray(parNode?.children) ? parNode.children.length : 0;
  const expectedPairs = childCount > 1 ? (childCount * (childCount - 1)) / 2 : 0;

  const smtA = emitSMT(ir);
  const smtB = emitSMT(ir);
  assert.equal(smtA, smtB, 'emission should be deterministic across runs');
  assert.match(smtA, /\(assert \(not \(or conflict_/);
  const conflictDecls = smtA.match(/\(declare-const conflict_[^\s]+ Bool\)/g) || [];
  assert.equal(conflictDecls.length, expectedPairs);
});
