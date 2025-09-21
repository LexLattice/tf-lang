import test from 'node:test';
import assert from 'node:assert/strict';
import { readFile } from 'node:fs/promises';

import { parseDSL } from '../packages/tf-compose/src/parser.mjs';
import {
  emitParWriteSafety,
  emitCommutationEquiv,
} from '../packages/tf-l0-proofs/src/smt-props.mjs';

const catalogUrl = new URL('../packages/tf-l0-spec/spec/catalog.json', import.meta.url);
const catalogPromise = readFile(catalogUrl, 'utf8').then((raw) => JSON.parse(raw));

test('par write safety detects conflicting branch writes', async () => {
  const catalog = await catalogPromise;
  const ir = parseDSL(`authorize{
    par{
      write-object(uri="res://kv/x", key="a", value="1");
      write-object(uri="res://kv/x", key="b", value="2")
    }
  }`);
  const smt = emitParWriteSafety(ir, { catalog });
  assert.ok(smt.includes('(declare-sort URI 0)'), 'declares URI sort');
  assert.ok(smt.includes('(assert InParSameURI)'), 'asserts detected conflict');
  assert.ok(smt.includes('(assert (not InParSameURI))'), 'includes safety axiom');
  assert.ok(/\(check-sat\)\s*$/.test(smt), 'ends with check-sat');
});

test('par write safety omits conflict assertion when URIs differ', async () => {
  const catalog = await catalogPromise;
  const ir = parseDSL(`authorize{
    par{
      write-object(uri="res://kv/a", key="a", value="1");
      write-object(uri="res://kv/b", key="b", value="2")
    }
  }`);
  const smt = emitParWriteSafety(ir, { catalog });
  assert.ok(!smt.includes('(assert InParSameURI)'), 'no conflict assertion for safe flow');
  assert.ok(smt.includes('(assert (not InParSameURI))'), 'still encodes safety axiom');
  assert.ok(/\(check-sat\)\s*$/.test(smt), 'ends with check-sat');
});

test('observability/pure commutation emits disequality proof obligation', async () => {
  const catalog = await catalogPromise;
  const seqEP = parseDSL('emit-metric(key="hits", value="1") |> hash');
  const seqPE = parseDSL('hash |> emit-metric(key="hits", value="1")');
  const smt = emitCommutationEquiv(seqEP, seqPE, { catalog });
  assert.ok(smt.includes('(declare-sort Val 0)'), 'declares Val sort');
  assert.ok(smt.includes('(declare-fun E (Val) Val)'), 'declares E');
  assert.ok(smt.includes('(declare-fun P (Val) Val)'), 'declares P');
  assert.ok(
    smt.includes('(assert (forall ((x Val)) (= (E (P x)) (P (E x)))))'),
    'includes commutation law'
  );
  assert.ok(smt.includes('(define-fun outA () Val (P (E input)))'), 'encodes EP sequence');
  assert.ok(smt.includes('(define-fun outB () Val (E (P input)))'), 'encodes PE sequence');
  assert.ok(smt.includes('(assert (not (= outA outB)))'), 'asserts disequality');
  assert.ok(/\(check-sat\)\s*$/.test(smt), 'ends with check-sat');
});

test('property emitters are deterministic', async () => {
  const catalog = await catalogPromise;
  const seqEP = parseDSL('emit-metric(key="hits", value="1") |> hash');
  const seqPE = parseDSL('hash |> emit-metric(key="hits", value="1")');
  const parFlow = parseDSL(`authorize{
    par{
      write-object(uri="res://kv/x", key="a", value="1");
      write-object(uri="res://kv/x", key="b", value="2")
    }
  }`);
  const parFirst = emitParWriteSafety(parFlow, { catalog });
  const parSecond = emitParWriteSafety(parFlow, { catalog });
  assert.equal(parFirst, parSecond, 'par safety emitter is deterministic');
  const commuteFirst = emitCommutationEquiv(seqEP, seqPE, { catalog });
  const commuteSecond = emitCommutationEquiv(seqEP, seqPE, { catalog });
  assert.equal(commuteFirst, commuteSecond, 'commutation emitter is deterministic');
});
