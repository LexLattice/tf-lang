import test from 'node:test';
import assert from 'node:assert/strict';
import { mkdtemp, readdir, readFile, rm } from 'node:fs/promises';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { fileURLToPath } from 'node:url';
import { execFile } from 'node:child_process';
import { promisify } from 'node:util';

import { emitLaw } from '../packages/tf-l0-proofs/src/smt-laws.mjs';

const execFileAsync = promisify(execFile);
const __dirname = fileURLToPath(new URL('.', import.meta.url));
const repoRoot = join(__dirname, '..');

function lawIncludes(text, snippet, message) {
  assert.ok(text.includes(snippet), message);
}

test('write idempotent law models repeated writes', () => {
  const text = emitLaw('idempotent:write-by-key');
  lawIncludes(
    text,
    '(define-fun once ((x Val) (u URI) (k Key) (ik IdKey) (v Val)) Val (W u k ik v))',
    'defines once helper'
  );
  lawIncludes(
    text,
    '(define-fun twice ((x Val) (u URI) (k Key) (ik IdKey) (v Val)) Val (W u k ik v))',
    'defines twice helper'
  );
  lawIncludes(
    text,
    '(assert (not (= (twice x u k ik v) (once x u k ik v))))',
    'asserts disequality for duplicate write pipeline'
  );
  assert.ok(text.trim().endsWith('(check-sat)'), 'write law terminates with check-sat');
});

test('serialize/deserialize law encodes both directions', () => {
  const text = emitLaw('inverse:serialize-deserialize');
  lawIncludes(text, '(forall ((v Val)) (= (D (S v)) v))', 'includes forward quantifier');
  lawIncludes(text, '(forall ((b Bytes)) (= (S (D b)) b))', 'includes reverse quantifier');
  assert.ok(text.trim().endsWith('(check-sat)'), 'inverse law terminates with check-sat');
});

test('suite emission is deterministic', async () => {
  const baseDir = await mkdtemp(join(tmpdir(), 'smt-laws-suite-'));
  const firstDir = join(baseDir, 'first');
  const secondDir = join(baseDir, 'second');
  const script = join(repoRoot, 'scripts', 'emit-smt-laws-suite.mjs');

  try {
    await execFileAsync('node', [script, '-o', firstDir], { cwd: repoRoot });
    await execFileAsync('node', [script, '-o', secondDir], { cwd: repoRoot });

    const first = await readDirContents(firstDir);
    const second = await readDirContents(secondDir);
    assert.deepEqual(first, second);
  } finally {
    await rm(baseDir, { recursive: true, force: true });
  }
});

async function readDirContents(dir) {
  const entries = await readdir(dir);
  entries.sort((a, b) => a.localeCompare(b));
  const result = {};
  for (const entry of entries) {
    result[entry] = await readFile(join(dir, entry), 'utf8');
  }
  return result;
}
