import test from 'node:test';
import assert from 'node:assert/strict';

import { parseDSL } from '../packages/tf-compose/src/parser.mjs';
import { emitParWriteSafety, emitCommutationEquiv } from '../packages/tf-l0-proofs/src/smt-props.mjs';

test('par-safety emits unsat proof when URIs clash', () => {
  const ir = parseDSL(`authorize{
    par{
      write-object(uri="res://kv/x", key="a", value="1");
      write-object(uri="res://kv/x", key="b", value="2")
    }
  }`);
  const smt = emitParWriteSafety(ir);
  assert.ok(smt.includes('(declare-fun InParSameURI () Bool)'), 'declares predicate');
  assert.ok(smt.includes('(assert InParSameURI)'), 'asserts presence of conflict');
  assert.ok(smt.includes('(assert (not InParSameURI))'), 'includes safety axiom');
  assert.ok(/\(check-sat\)\s*$/.test(smt), 'ends with check-sat');
});

test('par-safety stays sat when URIs differ', () => {
  const ir = parseDSL(`authorize{
    par{
      write-object(uri="res://kv/a", key="a", value="1");
      write-object(uri="res://kv/b", key="b", value="2")
    }
  }`);
  const first = emitParWriteSafety(ir);
  const second = emitParWriteSafety(ir);
  assert.equal(first, second, 'deterministic output');
  assert.ok(!first.includes('(assert InParSameURI)'), 'no conflict assertion');
  assert.ok(first.includes('(assert (not InParSameURI))'), 'safety axiom remains');
  assert.ok(/\(check-sat\)\s*$/.test(first), 'ends with check-sat');
});

test('commutation emitter encodes disequality under commuting law', () => {
  const seqEP = parseDSL(`authorize{
    seq{
      emit-metric(name="hits", value=1);
      hash-bytes(value="payload")
    }
  }`);
  const seqPE = parseDSL(`authorize{
    seq{
      hash-bytes(value="payload");
      emit-metric(name="hits", value=1)
    }
  }`);
  const first = emitCommutationEquiv(seqEP, seqPE);
  const second = emitCommutationEquiv(seqEP, seqPE);
  assert.equal(first, second, 'deterministic output');
  assert.ok(first.includes('(declare-sort Val 0)'), 'declares Val sort');
  assert.ok(first.includes('(declare-fun E (Val) Val)'), 'declares E');
  assert.ok(first.includes('(declare-fun P (Val) Val)'), 'declares P');
  assert.ok(/\(assert \(forall \(\(x Val\)\) \(= \(E \(P x\)\) \(P \(E x\)\)\)\)\)/.test(first), 'includes commuting law');
  assert.ok(first.includes('(assert (not (= outA outB)))'), 'asserts disequality');
  assert.ok(/\(check-sat\)\s*$/.test(first), 'ends with check-sat');
});
