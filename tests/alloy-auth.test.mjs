import test from 'node:test';
import assert from 'node:assert/strict';
import { readFile } from 'node:fs/promises';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';

import { parseDSL } from '../packages/tf-compose/src/parser.mjs';
import { emitAlloyAuth } from '../packages/tf-l0-proofs/src/alloy-auth.mjs';

const __dirname = dirname(fileURLToPath(import.meta.url));
const repoRoot = resolve(__dirname, '..');
const flowsDir = join(repoRoot, 'examples', 'flows');

const primIndexPromise = loadPrimIndex();

test('authorize dominance model flags missing coverage', async () => {
  const ir = await loadFlow('auth_missing.tf');
  const primIndex = await primIndexPromise;
  const alloy = emitAlloyAuth(ir, { primIndex });

  assert.ok(alloy.includes('pred MissingAuth { some n:Prim | some n.scopeNeed and not Covered[n] }'));
  assert.ok(alloy.includes('pred Covered[n:Prim] { some r:Region | Dominates[r, n] and some (r.scopes & n.scopeNeed) }'));
  assert.ok(alloy.includes('run { MissingAuth }'));
  assert.ok(alloy.includes('run { not MissingAuth }'));
  assert.ok(/Scope_kms_sign/.test(alloy), 'declares kms.sign scope atom');
  assert.ok(/PrimScopeNeeds\s*\{[\s\S]*Scope_kms_sign/.test(alloy), 'links prim to scope need');
});

test('authorize dominance model is deterministic and includes runs when covered', async () => {
  const ir = await loadFlow('auth_ok.tf');
  const primIndex = await primIndexPromise;
  const first = emitAlloyAuth(ir, { primIndex });
  const second = emitAlloyAuth(ir, { primIndex });

  assert.equal(first, second, 'emission is deterministic');
  assert.ok(first.includes('pred MissingAuth'));
  assert.ok(first.includes('run { MissingAuth }'));
  assert.ok(first.includes('run { not MissingAuth }'));
});

async function loadFlow(filename) {
  const raw = await readFile(join(flowsDir, filename), 'utf8');
  return parseDSL(raw);
}

async function loadPrimIndex() {
  const [catalogRaw, scopesRaw] = await Promise.all([
    readFile(join(repoRoot, 'packages/tf-l0-spec/spec/catalog.json'), 'utf8'),
    readFile(join(repoRoot, 'packages/tf-l0-check/rules/authorize-scopes.json'), 'utf8'),
  ]);
  const catalog = JSON.parse(catalogRaw);
  const scopeRules = JSON.parse(scopesRaw);
  const map = new Map();
  const prims = Array.isArray(catalog?.primitives) ? catalog.primitives : [];
  for (const prim of prims) {
    if (!prim || typeof prim.name !== 'string') {
      continue;
    }
    const key = prim.name.toLowerCase();
    const id = typeof prim.id === 'string' ? prim.id : prim.name;
    const scopes = Array.isArray(scopeRules?.[id]) ? scopeRules[id] : [];
    map.set(key, { id, scopes });
  }
  return map;
}
