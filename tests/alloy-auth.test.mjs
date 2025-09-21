import test from 'node:test';
import assert from 'node:assert/strict';
import { readFile } from 'node:fs/promises';
import { join } from 'node:path';
import { fileURLToPath } from 'node:url';

import { emitAuthorizeAlloy } from '../packages/tf-l0-proofs/src/alloy-auth.mjs';
import { parseDSL } from '../packages/tf-compose/src/parser.mjs';

const __dirname = fileURLToPath(new URL('.', import.meta.url));
const repoRoot = join(__dirname, '..');

async function loadFlow(name) {
  const sourcePath = join(repoRoot, 'examples', 'flows', name);
  const raw = await readFile(sourcePath, 'utf8');
  return parseDSL(raw);
}

test('auth_missing model exposes MissingAuth run', async () => {
  const ir = await loadFlow('auth_missing.tf');
  const alloy = emitAuthorizeAlloy(ir);

  assertOrder(
    alloy,
    [
      'sig Node {}',
      'pred Dominates[r: Region, n: Node] { n in r.*children }',
      'pred Covered[n: Prim] { some r: Region | Dominates[r, n] and some (r.scopes & n.scopeNeed) }',
      'pred MissingAuth { some n: Prim | some n.scopeNeed and not Covered[n] }',
      'run { MissingAuth }',
      'run { not MissingAuth }'
    ]
  );

  assert.ok(alloy.includes('Prim0.scopeNeed = Scope0'), 'annotates protected prim scope');
});

test('auth_ok model remains deterministic', async () => {
  const ir = await loadFlow('auth_ok.tf');
  const first = emitAuthorizeAlloy(ir);
  const second = emitAuthorizeAlloy(ir);

  assert.ok(first.includes('pred MissingAuth'), 'includes MissingAuth predicate');
  assert.ok(first.includes('run { MissingAuth }'), 'includes run MissingAuth command');
  assert.ok(first.includes('run { not MissingAuth }'), 'includes negated run command');
  assert.equal(first, second, 'emission is deterministic');
});

function assertOrder(text, segments) {
  let cursor = -1;
  for (const segment of segments) {
    const index = text.indexOf(segment);
    assert.ok(index >= 0, `expected segment ${segment}`);
    assert.ok(index > cursor, `segment ${segment} should follow previous content`);
    cursor = index;
  }
}
