// @tf-test kind=proofs area=smt speed=medium deps=node
import test from 'node:test';
import assert from 'node:assert/strict';

import {
  emitLaw,
  emitFlowEquivalence,
} from '../packages/tf-l0-proofs/src/smt-laws.mjs';

test('law axioms emit expected quantifiers', () => {
  const idempotent = emitLaw('idempotent:hash');
  assert.ok(
    idempotent.includes('(forall ((x Val)) (= (H (H x)) (H x)))'),
    'idempotent law includes quantifier'
  );
  assert.ok(idempotent.endsWith('(check-sat)\n'), 'idempotent law ends with check-sat');

  const inverse = emitLaw('inverse:serialize-deserialize');
  assert.ok(
    inverse.includes('(forall ((v Val)) (= (D (S v)) v))'),
    'inverse law includes quantifier'
  );
  assert.ok(
    inverse.includes('(forall ((b Bytes)) (= (S (D b)) b))'),
    'inverse law includes symmetric quantifier'
  );
  assert.ok(inverse.endsWith('(check-sat)\n'), 'inverse law ends with check-sat');

  const commute = emitLaw('commute:emit-metric-with-pure');
  assert.ok(
    commute.includes('(forall ((x Val)) (= (E (H x)) (H (E x))))'),
    'commute law includes quantifier'
  );
  assert.ok(commute.endsWith('(check-sat)\n'), 'commute law ends with check-sat');
});

test('law emission is deterministic', () => {
  const first = emitLaw('idempotent:hash');
  const second = emitLaw('idempotent:hash');
  assert.equal(first, second);
});

test('flow equivalence encodes commute obligation', () => {
  const smt = emitFlowEquivalence(
    ['emit-metric', 'hash'],
    ['hash', 'emit-metric'],
    ['commute:emit-metric-with-pure']
  );
  assert.ok(
    smt.includes('(assert (not (= outA outB)))'),
    'flow equivalence asserts disequality'
  );
  assert.ok(
    smt.includes('(forall ((x Val)) (= (E (H x)) (H (E x))))'),
    'axioms mention commute law'
  );
  assert.ok(/\(declare-fun\s+E\s+\(Val\)\s+Val\)/.test(smt), 'declares E function');
  assert.ok(/\(declare-fun\s+H\s+\(Val\)\s+Val\)/.test(smt), 'declares H function');
  assert.ok(smt.trim().endsWith('(check-sat)'), 'equivalence ends with check-sat');
});

test('flow equivalence respects domain boundaries', () => {
  assert.doesNotThrow(() =>
    emitFlowEquivalence(
      ['deserialize'],
      ['deserialize'],
      ['inverse:serialize-deserialize']
    )
  );

  assert.throws(
    () => emitFlowEquivalence(['deserialize'], ['hash'], []),
    /Flow domains must match/
  );

  assert.throws(
    () => emitFlowEquivalence(['serialize'], ['hash'], []),
    /Flow codomains must match/
  );
});

test('flow equivalence emission is deterministic', () => {
  const flowA = ['emit-metric', 'hash'];
  const flowB = ['hash', 'emit-metric'];
  const laws = ['commute:emit-metric-with-pure'];
  const first = emitFlowEquivalence(flowA, flowB, laws);
  const second = emitFlowEquivalence(flowA, flowB, laws);
  assert.equal(first, second);
});
