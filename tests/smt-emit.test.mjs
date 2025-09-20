import test from 'node:test';
import assert from 'node:assert/strict';
import { readFile } from 'node:fs/promises';

import { parseDSL } from '../packages/tf-compose/src/parser.mjs';
import { emitSMT } from '../packages/tf-l0-proofs/src/smt.mjs';

async function loadIR(path) {
  const source = await readFile(path, 'utf8');
  return parseDSL(source);
}

function countParPairs(node) {
  if (!node || typeof node !== 'object') {
    return 0;
  }

  let total = 0;
  if (node.node === 'Par' && Array.isArray(node.children)) {
    const n = node.children.length;
    total += (n * (n - 1)) / 2;
  }

  if (Array.isArray(node.children)) {
    for (const child of node.children) {
      total += countParPairs(child);
    }
  }

  return total;
}

test('emitSMT encodes storage conflict flow', async () => {
  const ir = await loadIR('examples/flows/storage_conflict.tf');
  const smt = emitSMT(ir);
  const again = emitSMT(ir);
  assert.equal(smt, again, 'SMT emission must be deterministic');

  assert.ok(smt.includes('(assert (not (or'), 'final assert missing');
  assert.ok(smt.trim().endsWith('(check-sat)'), 'missing check-sat');

  const decls = smt.match(/\(declare-const conflict_[^\s]* Bool\)/g) || [];
  const expectedPairs = countParPairs(ir);
  assert.equal(decls.length, expectedPairs, 'pair count mismatch');
  assert.ok(decls.length > 0, 'expected at least one conflict declaration');
});

test('emitSMT encodes storage ok flow', async () => {
  const ir = await loadIR('examples/flows/storage_ok.tf');
  const smt = emitSMT(ir);
  const again = emitSMT(ir);
  assert.equal(smt, again, 'SMT emission must be deterministic');

  assert.ok(smt.includes('(assert (not (or'), 'final assert missing');
  assert.ok(smt.trim().endsWith('(check-sat)'), 'missing check-sat');

  const decls = smt.match(/\(declare-const conflict_[^\s]* Bool\)/g) || [];
  const expectedPairs = countParPairs(ir);
  assert.equal(decls.length, expectedPairs, 'pair count mismatch');
});
