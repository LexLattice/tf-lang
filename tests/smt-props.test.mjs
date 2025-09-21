import test from 'node:test';
import assert from 'node:assert/strict';

import { parseDSL } from '../packages/tf-compose/src/parser.mjs';
import {
  emitParWriteSafety,
  emitCommutationEquiv,
} from '../packages/tf-l0-proofs/src/smt-props.mjs';

test('par write safety detects conflicting URIs', () => {
  const ir = parseDSL(
    'par{ write-object(uri="res://kv/x", value="1"); write-object(uri="res://kv/x", value="2") }'
  );
  const smt = emitParWriteSafety(ir);
  assert.ok(smt.includes('(declare-sort URI 0)'));
  assert.ok(smt.includes('(declare-fun InParSameURI () Bool)'));
  assert.ok(smt.includes('(assert InParSameURI)'));
  assert.ok(smt.includes('(assert (not InParSameURI))'));
  assert.ok(smt.includes('(check-sat)'));

  const again = emitParWriteSafety(ir);
  assert.strictEqual(smt, again);
});

test('par write safety skips when URIs differ', () => {
  const ir = parseDSL(
    'par{ write-object(uri="res://kv/x", value="1"); write-object(uri="res://kv/y", value="2") }'
  );
  const smt = emitParWriteSafety(ir);
  assert.ok(!smt.includes('(assert InParSameURI)'));
  assert.ok(smt.includes('(assert (not InParSameURI))'));
  assert.ok(smt.includes('(check-sat)'));
});

test('commutation equivalence emits law and disequality', () => {
  const seqEP = parseDSL('emit-metric |> hash');
  const seqPE = parseDSL('hash |> emit-metric');
  const smt = emitCommutationEquiv(seqEP, seqPE);

  assert.ok(smt.includes('(declare-sort Val 0)'));
  assert.ok(smt.includes('(declare-fun E (Val) Val)'));
  assert.ok(smt.includes('(declare-fun P (Val) Val)'));
  assert.ok(smt.includes('(assert (forall ((x Val)) (= (E (P x)) (P (E x)))))'));
  assert.ok(smt.includes('(assert (not (= outA outB)))'));
  assert.ok(smt.includes('(check-sat)'));

  const again = emitCommutationEquiv(seqEP, seqPE);
  assert.strictEqual(smt, again);
});
