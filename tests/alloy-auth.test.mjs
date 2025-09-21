import test from 'node:test';
import assert from 'node:assert/strict';
import { readFile } from 'node:fs/promises';
import path from 'node:path';
import { fileURLToPath } from 'node:url';

import { parseDSL } from '../packages/tf-compose/src/parser.mjs';
import { emitAlloyAuthorize } from '../packages/tf-l0-proofs/src/alloy-auth.mjs';

const __dirname = path.dirname(fileURLToPath(import.meta.url));
const repoRoot = path.resolve(__dirname, '..');
const rulesPath = path.join(repoRoot, 'packages', 'tf-l0-check', 'rules', 'authorize-scopes.json');
const rules = JSON.parse(await readFile(rulesPath, 'utf8'));

test('missing authorize scope model exposes counterexample run', async () => {
  const ir = await loadFlow('examples/flows/auth_missing.tf');
  const alloy = emitAlloyAuthorize(ir, { rules });

  assert.match(alloy, /pred MissingAuth/, 'model should define MissingAuth predicate');

  const runLines = collectRunLines(alloy);
  assert.deepEqual(runLines, ['run { MissingAuth }', 'run { not MissingAuth }']);
});

test('authorized prim model still includes dominance predicates', async () => {
  const ir = await loadFlow('examples/flows/auth_ok.tf');
  const alloy = emitAlloyAuthorize(ir, { rules });

  assert.match(alloy, /pred Covered\[n:Prim\]/, 'model should define Covered predicate');
  assert.match(alloy, /Scope_kms_sign/, 'model should declare the kms.sign scope symbol');

  const runLines = collectRunLines(alloy);
  assert.deepEqual(runLines, ['run { MissingAuth }', 'run { not MissingAuth }']);
});

test('authorize alloy emission is deterministic with ordered sections', async () => {
  const ir = await loadFlow('examples/flows/auth_ok.tf');
  const first = emitAlloyAuthorize(ir, { rules });
  const second = emitAlloyAuthorize(ir, { rules });
  assert.equal(first, second, 'emitter should be deterministic');

  const trimmed = first
    .split('\n')
    .map((line) => line.trim())
    .filter((line) => line.length > 0);

  const sigNodeIndex = trimmed.indexOf('sig Node {}');
  const sigRegionIndex = trimmed.indexOf('sig Region extends Node { scopes: set Scope, children: set Node }');
  const sigPrimIndex = trimmed.indexOf('sig Prim extends Node { primId: one String, scopeNeed: set Scope }');
  const predDominatesIndex = trimmed.indexOf('pred Dominates[r:Region, n:Node] { n in r.*children }');
  const runMissingIndex = trimmed.indexOf('run { MissingAuth }');
  const runNotMissingIndex = trimmed.indexOf('run { not MissingAuth }');

  assert.ok(sigNodeIndex >= 0 && sigNodeIndex < sigRegionIndex);
  assert.ok(sigRegionIndex < sigPrimIndex);
  assert.ok(predDominatesIndex > sigPrimIndex);
  assert.ok(runMissingIndex > predDominatesIndex);
  assert.equal(runNotMissingIndex, runMissingIndex + 1);
});

async function loadFlow(relPath) {
  const source = await readFile(path.join(repoRoot, relPath), 'utf8');
  return parseDSL(source);
}

function collectRunLines(alloy) {
  return alloy
    .split('\n')
    .map((line) => line.trim())
    .filter((line) => line.startsWith('run {'));
}

