import test from 'node:test';
import assert from 'node:assert/strict';

import { parseDSL } from '../packages/tf-compose/src/parser.mjs';
import {
  emitParWriteSafety,
  emitCommutationEquiv,
} from '../packages/tf-l0-proofs/src/smt-props.mjs';

test('par write safety detects conflicting URIs across nested branches', () => {
  const ir = parseDSL(
    'par{ seq{ write-object(uri="res://kv/x", value="1") }; seq{ par{ write-object(uri="res://kv/x", value="2"); write-object(uri="res://kv/y", value="3") } } }'
  );
  const smt = emitParWriteSafety(ir);
  assert.ok(smt.startsWith('; par write safety'));
  assert.ok(smt.includes('(declare-sort URI 0)'));
  assert.ok(smt.includes('(declare-fun InParSameURI () Bool)'));
  assert.ok(smt.includes('(assert (not InParSameURI))'));
  assert.ok(smt.includes('(assert (= InParSameURI true))'));
  assert.ok(smt.trimEnd().endsWith('(check-sat)'));
  assert.ok(smt.endsWith('\n'));

  const axiomIndex = smt.indexOf('(assert (not InParSameURI))');
  const bakedIndex = smt.indexOf('(assert (= InParSameURI true))');
  assert.ok(axiomIndex < bakedIndex, 'axiom appears before IR assertion');

  const again = emitParWriteSafety(ir);
  assert.strictEqual(smt, again);
});

test('par write safety notes absence of conflicts when URIs differ', () => {
  const ir = parseDSL(
    'par{ write-object(uri="res://kv/x", value="1"); write-object(uri="res://kv/y", value="2") }'
  );
  const smt = emitParWriteSafety(ir);
  assert.ok(smt.includes('(assert (= InParSameURI false))'));
  assert.ok(!smt.includes('(assert (= InParSameURI true))'));
  assert.ok(smt.includes('(assert (not InParSameURI))'));
  assert.ok(smt.trimEnd().endsWith('(check-sat)'));
});

test('commutation equivalence emits axioms, encodings, and disequality goal', () => {
  const seqEP = parseDSL('emit-metric |> hash');
  const seqPE = parseDSL('hash |> emit-metric');
  const smt = emitCommutationEquiv(seqEP, seqPE);

  assert.ok(smt.startsWith('; observability/pure commutation equivalence'));
  assert.ok(smt.includes('(declare-sort Val 0)'));
  assert.ok(smt.includes('(declare-fun E (Val) Val)'));
  assert.ok(smt.includes('(declare-fun P (Val) Val)'));
  assert.ok(smt.includes('(assert (forall ((x Val)) (= (E (P x)) (P (E x)))))'));
  assert.ok(smt.includes('(declare-const x Val)'));
  assert.ok(smt.includes('(define-fun outA () Val'));
  assert.ok(smt.includes('(define-fun outB () Val'));
  assert.ok(smt.includes('(assert (not (= outA outB)))'));
  assert.ok(smt.trimEnd().endsWith('(check-sat)'));

  const again = emitCommutationEquiv(seqEP, seqPE);
  assert.strictEqual(smt, again);
});
