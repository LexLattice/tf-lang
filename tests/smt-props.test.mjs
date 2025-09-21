import test from 'node:test';
import assert from 'node:assert/strict';
import { readFile } from 'node:fs/promises';

import { parseDSL } from '../packages/tf-compose/src/parser.mjs';
import {
  emitParWriteSafety,
  emitCommutationEquiv,
} from '../packages/tf-l0-proofs/src/smt-props.mjs';

const catalog = await loadCatalog();

test('par safety detects same-uri writes', () => {
  const ir = parseDSL(
    'par{ write-object(uri="res://kv/x", key="a", value="1"); write-object(uri="res://kv/x", key="b", value="2") }'
  );
  const smt = emitParWriteSafety(ir, { catalog });
  assert.ok(smt.includes('(assert InParSameURI)'), 'conflict assertion present');
  assert.ok(smt.includes('(assert (not InParSameURI))'), 'safety axiom asserted');
  assert.ok(smt.trim().endsWith('(check-sat)'), 'ends with check-sat');
});

test('par safety skips distinct URIs', () => {
  const ir = parseDSL(
    'par{ write-object(uri="res://kv/x", key="a", value="1"); write-object(uri="res://kv/y", key="b", value="2") }'
  );
  const smt = emitParWriteSafety(ir, { catalog });
  assert.ok(!smt.includes('(assert InParSameURI)'), 'no same-URI assertion when safe');
  assert.ok(smt.includes('(assert (not InParSameURI))'), 'safety axiom still asserted');
});

test('commutation equivalence encodes axioms and disequality', () => {
  const seqEP = parseDSL('emit-metric(key="ok") |> hash');
  const seqPE = parseDSL('hash |> emit-metric(key="ok")');
  const smt = emitCommutationEquiv(seqEP, seqPE, { catalog });
  assert.ok(/\(declare-sort\s+Val\s+0\)/.test(smt), 'declares Val sort');
  assert.ok(/\(declare-fun\s+E\s+\(Val\)\s+Val\)/.test(smt), 'declares E function');
  assert.ok(/\(declare-fun\s+P\s+\(Val\)\s+Val\)/.test(smt), 'declares P function');
  assert.ok(
    smt.includes('(assert (forall ((x Val)) (= (E (P x)) (P (E x)))))'),
    'includes commutation law'
  );
  assert.ok(smt.includes('(assert (not (= outA outB)))'), 'asserts disequality');
  assert.ok(smt.trim().endsWith('(check-sat)'), 'ends with check-sat');
});

test('commutation emitter is deterministic', () => {
  const seqEP = parseDSL('emit-metric(key="ok") |> hash');
  const seqPE = parseDSL('hash |> emit-metric(key="ok")');
  const first = emitCommutationEquiv(seqEP, seqPE, { catalog });
  const second = emitCommutationEquiv(seqEP, seqPE, { catalog });
  assert.equal(first, second);
});

test('par safety emitter is deterministic', () => {
  const ir = parseDSL(
    'par{ write-object(uri="res://kv/x", key="a", value="1"); write-object(uri="res://kv/y", key="b", value="2") }'
  );
  const first = emitParWriteSafety(ir, { catalog });
  const second = emitParWriteSafety(ir, { catalog });
  assert.equal(first, second);
});

async function loadCatalog() {
  try {
    const raw = await readFile('packages/tf-l0-spec/spec/catalog.json', 'utf8');
    return JSON.parse(raw);
  } catch {
    return { primitives: [] };
  }
}
