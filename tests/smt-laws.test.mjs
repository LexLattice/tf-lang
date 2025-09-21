import test from 'node:test';
import assert from 'node:assert/strict';

import { emitLaw, emitFlowEquivalence } from '../packages/tf-l0-proofs/src/smt-laws.mjs';

test('idempotent law axiom emits expected forall', () => {
  const smt = emitLaw('idempotent:hash');
  assert.match(
    smt,
    /\(assert \(forall \(\(x Val\)\) \(= \(H \(H x\)\) \(H x\)\)\)\)/
  );
  assert.ok(smt.trim().endsWith('(check-sat)'));
});

test('inverse law axiom includes serialize/deserialize relation', () => {
  const smt = emitLaw('inverse:serialize-deserialize');
  assert.match(
    smt,
    /\(assert \(forall \(\(v Val\)\) \(= \(D \(S v\)\) v\)\)\)/
  );
  assert.ok(smt.includes('(declare-fun S (Val) Bytes)'));
  assert.ok(smt.includes('(declare-fun D (Bytes) Val)'));
});

test('commute law axiom defaults to generic pure function', () => {
  const smt = emitLaw('commute:emit-metric-with-pure');
  assert.match(
    smt,
    /\(assert \(forall \(\(x Val\)\) \(= \(E \(P x\)\) \(P \(E x\)\)\)\)\)/
  );
});

test('flow equivalence under commute law references emit and hash', () => {
  const smt = emitFlowEquivalence(
    'emit-metric |> hash',
    'hash |> emit-metric',
    ['commute:emit-metric-with-pure']
  );
  assert.ok(smt.includes('(assert (not (= outA outB)))'));
  assert.match(
    smt,
    /\(assert \(forall \(\(x Val\)\) \(= \(E \(H x\)\) \(H \(E x\)\)\)\)\)/
  );
});

test('emissions are deterministic', () => {
  const a1 = emitLaw('idempotent:hash');
  const a2 = emitLaw('idempotent:hash');
  assert.equal(a1, a2);

  const e1 = emitFlowEquivalence(
    'serialize |> deserialize',
    'serialize |> deserialize',
    ['inverse:serialize-deserialize']
  );
  const e2 = emitFlowEquivalence(
    'serialize |> deserialize',
    'serialize |> deserialize',
    ['inverse:serialize-deserialize']
  );
  assert.equal(e1, e2);
});
