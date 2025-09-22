// @tf-test kind=proofs area=alloy speed=fast deps=node
import test from 'node:test';
import assert from 'node:assert/strict';
import { readFile } from 'node:fs/promises';
import { parseDSL } from '../packages/tf-compose/src/parser.mjs';
import { emitAuthorizeAlloy } from '../packages/tf-l0-proofs/src/alloy-auth.mjs';

const flowsDir = new URL('../examples/flows/', import.meta.url);
const rulesPromise = loadRules();

async function loadRules() {
  const rulesUrl = new URL('../packages/tf-l0-check/rules/authorize-scopes.json', import.meta.url);
  const raw = await readFile(rulesUrl, 'utf8');
  return JSON.parse(raw);
}

async function loadFlow(name) {
  const flowUrl = new URL(name, flowsDir);
  const raw = await readFile(flowUrl, 'utf8');
  return parseDSL(raw);
}

test('authorize dominance model highlights missing scopes', async () => {
  const [rules, ir] = await Promise.all([rulesPromise, loadFlow('auth_missing.tf')]);
  const alloy = emitAuthorizeAlloy(ir, { rules });

  assert.ok(alloy.startsWith('open util/ordering[Node]'), 'model should open util ordering');
  assert.match(alloy, /pred MissingAuth/);
  assertSectionOrdering(alloy);
  assert.match(alloy, /run \{ MissingAuth \}/);
  assert.match(alloy, /run \{ not MissingAuth \}/);
  assert.match(alloy, /Prim0\.primId = "tf:security\/sign-data@1"/);
  assert.match(alloy, /Prim0\.scopeNeed =/);
});

test('covered scopes retain predicates and commands', async () => {
  const [rules, ir] = await Promise.all([rulesPromise, loadFlow('auth_ok.tf')]);
  const alloy = emitAuthorizeAlloy(ir, { rules });

  assert.match(alloy, /pred Dominates/);
  assert.match(alloy, /pred Covered/);
  assertSectionOrdering(alloy);
  assert.match(alloy, /run \{ MissingAuth \}/);
  assert.match(alloy, /run \{ not MissingAuth \}/);
  assert.match(alloy, /Region0\.children =/);
});

test('authorize alloy emission is deterministic', async () => {
  const [rules, ir] = await Promise.all([rulesPromise, loadFlow('auth_ok.tf')]);
  const first = emitAuthorizeAlloy(ir, { rules });
  const second = emitAuthorizeAlloy(ir, { rules });
  assert.equal(first, second);
});

test('scope hints propagate to run commands', async () => {
  const [rules, ir] = await Promise.all([rulesPromise, loadFlow('auth_ok.tf')]);
  const alloy = emitAuthorizeAlloy(ir, { rules, scope: 7 });

  assert.ok(alloy.includes('run { MissingAuth } for 7'));
  assert.ok(alloy.includes('run { not MissingAuth } for 7'));
});

function assertSectionOrdering(text) {
  const sigIndex = text.indexOf('sig Node {}');
  const predIndex = text.indexOf('pred Dominates');
  const runIndex = text.indexOf('run { MissingAuth }');
  assert.ok(sigIndex >= 0, 'signature section should exist');
  assert.ok(predIndex > sigIndex, 'predicate section should follow signatures');
  assert.ok(runIndex > predIndex, 'run commands should follow predicates');
}
