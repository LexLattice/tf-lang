import test from 'node:test';
import assert from 'node:assert/strict';
import { readFile } from 'node:fs/promises';

import { parseDSL } from '../packages/tf-compose/src/parser.mjs';
import { emitSMT } from '../packages/tf-l0-proofs/src/smt.mjs';

const conflictFlow = new URL('../examples/flows/storage_conflict.tf', import.meta.url);
const okFlow = new URL('../examples/flows/storage_ok.tf', import.meta.url);

async function loadIR(url) {
  const source = await readFile(url, 'utf8');
  return parseDSL(source);
}

test('storage_conflict emits conflict assertions', async () => {
  const ir = await loadIR(conflictFlow);
  const smt = emitSMT(ir);
  assert.ok(/\(assert \(not \(or/.test(smt), 'should include global validity assert');
  const declared = smt.match(/\(declare-const\s+conflict_/g) || [];
  assert.ok(declared.length >= 1, 'at least one conflict declared');
  assert.ok(/\(check-sat\)\s*$/.test(smt), 'ends with check-sat');
});

test('storage_ok emits deterministic model without conflicts', async () => {
  const ir = await loadIR(okFlow);
  const first = emitSMT(ir);
  const second = emitSMT(ir);
  assert.equal(first, second, 'emission is deterministic');
  const declared = first.match(/\(declare-const\s+conflict_/g) || [];
  assert.equal(declared.length, 0, 'no conflicts declared for sequential flow');
  assert.ok(first.includes('(assert (not (or)))'), 'validity assert handles empty ors');
  assert.ok(/\(check-sat\)\s*$/.test(first), 'ends with check-sat');
});
