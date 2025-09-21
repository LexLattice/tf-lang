import test from 'node:test';
import assert from 'node:assert/strict';

import { parseDSL } from '../packages/tf-compose/src/parser.mjs';
import {
  emitLaw,
  emitFlowEquivalence
} from '../packages/tf-l0-proofs/src/smt-laws.mjs';

test('law axioms emit expected forall assertions', () => {
  const idempotent = emitLaw('idempotent:hash');
  assert.ok(
    idempotent.includes('(forall ((x Val)) (= (H (H x)) (H x)))'),
    'idempotent law should assert H idempotency'
  );
  assert.ok(/\(check-sat\)\s*$/.test(idempotent), 'idempotent law ends with check-sat');

  const inverse = emitLaw('inverse:serialize-deserialize');
  assert.ok(
    inverse.includes('(forall ((v Val)) (= (D (S v)) v))'),
    'inverse law should assert deserialize(serialize(v)) = v'
  );
  assert.ok(/\(check-sat\)\s*$/.test(inverse), 'inverse law ends with check-sat');

  const commute = emitLaw('commute:emit-metric-with-pure');
  assert.ok(
    commute.includes('(forall ((x Val)) (= (E (H x)) (H (E x))))'),
    'commute law should assert emit/hash commutativity'
  );
  assert.ok(/\(check-sat\)\s*$/.test(commute), 'commute law ends with check-sat');
});

test('flow equivalence encodes witness with commute axiom', () => {
  const left = parseDSL('emit-metric |> hash');
  const right = parseDSL('hash |> emit-metric');
  const smt = emitFlowEquivalence(left, right, ['commute:emit-metric-with-pure']);
  assert.ok(
    smt.includes('(assert (not (= outA outB)))'),
    'equivalence should negate equality for solver check'
  );
  assert.ok(
    smt.includes('(forall ((x Val)) (= (E (H x)) (H (E x))))'),
    'commute axiom should mention both E and H'
  );
});

test('emission is deterministic', () => {
  const lawFirst = emitLaw('inverse:serialize-deserialize');
  const lawSecond = emitLaw('inverse:serialize-deserialize');
  assert.equal(lawFirst, lawSecond, 'law emission should be deterministic');

  const ir = parseDSL('hash |> hash');
  const first = emitFlowEquivalence(ir, ir, ['idempotent:hash']);
  const second = emitFlowEquivalence(ir, ir, ['idempotent:hash']);
  assert.equal(first, second, 'flow equivalence emission should be deterministic');
});
