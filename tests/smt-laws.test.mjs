import test from 'node:test';
import assert from 'node:assert/strict';

import { emitLaw, emitFlowEquivalence } from '../packages/tf-l0-proofs/src/smt-laws.mjs';

test('idempotent law axiom emitted with check-sat', () => {
  const out = emitLaw('idempotent:hash');
  assert.ok(out.includes('(forall ((x Val)) (= (H (H x)) (H x))))'));
  assert.ok(out.includes('(declare-fun H (Val) Val)'));
  assert.ok(out.endsWith('(check-sat)\n'));
});

test('inverse law axiom emitted with check-sat', () => {
  const out = emitLaw('inverse:serialize-deserialize');
  assert.ok(out.includes('(forall ((v Val)) (= (D (S v)) v)))'));
  assert.ok(out.includes('(declare-fun S (Val) Bytes)'));
  assert.ok(out.includes('(declare-fun D (Bytes) Val)'));
  assert.ok(out.endsWith('(check-sat)\n'));
});

test('commute law axiom references emit and hash', () => {
  const out = emitLaw('commute:emit-metric-with-pure');
  assert.ok(out.includes('(forall ((x Val)) (= (E (H x)) (H (E x)))))'));
  assert.ok(out.includes('(declare-fun E (Val) Val)'));
  assert.ok(out.endsWith('(check-sat)\n'));
});

test('flow equivalence embeds axiom and disequality witness', () => {
  const out = emitFlowEquivalence(
    ['emit-metric', 'hash'],
    ['hash', 'emit-metric'],
    ['commute:emit-metric-with-pure']
  );
  assert.ok(out.includes('(assert (not (= outA outB)))'));
  assert.ok(out.includes('(assert (forall ((x Val)) (= (E (H x)) (H (E x)))))'));
  assert.ok(out.includes('(declare-const input Val)'));
});

test('law emission is deterministic', () => {
  const first = emitLaw('idempotent:hash');
  const second = emitLaw('idempotent:hash');
  assert.equal(first, second);
});
