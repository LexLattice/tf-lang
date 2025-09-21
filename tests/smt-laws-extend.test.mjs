import test from 'node:test';
import assert from 'node:assert/strict';
import { execFile } from 'node:child_process';
import { mkdtemp, readFile, readdir } from 'node:fs/promises';
import { tmpdir } from 'node:os';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';
import { promisify } from 'node:util';

import { emitLaw, emitFlowEquivalence } from '../packages/tf-l0-proofs/src/smt-laws.mjs';

const exec = promisify(execFile);
const __dirname = dirname(fileURLToPath(import.meta.url));
const repoRoot = resolve(__dirname, '..');

function tmpPath(prefix) {
  return mkdtemp(join(tmpdir(), prefix));
}

test('write idempotency law encodes repeated write collapse', () => {
  const smt = emitLaw('idempotent:write-by-key');
  assert.ok(smt.includes('(declare-fun W (URI Key IdKey Val) Val)'), 'declares write function');
  assert.ok(
    smt.includes('(assert (not (= (twice x u k ik v) (once x u k ik v))))'),
    'idempotent law asserts collapse'
  );
  assert.ok(smt.trim().endsWith('(check-sat)'), 'law ends with check-sat');
});

test('serialize/deserialize equivalence compares against identity', () => {
  const smt = emitFlowEquivalence(
    ['serialize', 'deserialize'],
    ['id'],
    ['inverse:serialize-deserialize']
  );
  assert.ok(
    smt.includes('(forall ((v Val)) (= (D (S v)) v))'),
    'includes forward roundtrip axiom'
  );
  assert.ok(
    smt.includes('(forall ((b Bytes)) (= (S (D b)) b))'),
    'includes reverse roundtrip axiom'
  );
  assert.ok(
    smt.includes('(assert (not (= outA outB)))'),
    'equivalence asserts disequality'
  );
  assert.ok(smt.trim().endsWith('(check-sat)'), 'equivalence ends with check-sat');
});

test('suite emitter is deterministic', async () => {
  const firstDir = await tmpPath('smt-laws-suite-');
  const secondDir = await tmpPath('smt-laws-suite-');

  await exec('node', ['scripts/emit-smt-laws-suite.mjs', '-o', firstDir], { cwd: repoRoot });
  await exec('node', ['scripts/emit-smt-laws-suite.mjs', '-o', secondDir], { cwd: repoRoot });

  const writeLaw = await readFile(join(firstDir, 'write_idempotent_by_key.smt2'), 'utf8');
  assert.ok(
    writeLaw.includes('(assert (not (= (twice x u k ik v) (once x u k ik v))))'),
    'write law captures idempotency'
  );
  assert.ok(writeLaw.trim().endsWith('(check-sat)'), 'write law ends with check-sat');

  const inverse = await readFile(join(firstDir, 'inverse_roundtrip.smt2'), 'utf8');
  assert.ok(
    inverse.includes('(forall ((b Bytes)) (= (S (D b)) b))'),
    'inverse roundtrip includes reverse axiom'
  );
  assert.ok(
    inverse.includes('(forall ((v Val)) (= (D (S v)) v))'),
    'inverse roundtrip includes forward axiom'
  );
  assert.ok(inverse.trim().endsWith('(check-sat)'), 'inverse file ends with check-sat');

  await assertDirectoriesEqual(firstDir, secondDir);
});

async function assertDirectoriesEqual(leftDir, rightDir) {
  const [leftFiles, rightFiles] = await Promise.all([
    listFiles(leftDir),
    listFiles(rightDir),
  ]);
  assert.deepEqual(leftFiles.map((f) => f.name), rightFiles.map((f) => f.name), 'file sets match');
  for (let i = 0; i < leftFiles.length; i++) {
    const leftContent = await readFile(join(leftDir, leftFiles[i].name), 'utf8');
    const rightContent = await readFile(join(rightDir, rightFiles[i].name), 'utf8');
    assert.equal(leftContent, rightContent, `content matches for ${leftFiles[i].name}`);
  }
}

async function listFiles(dir) {
  const entries = await readdir(dir, { withFileTypes: true });
  const files = entries.filter((entry) => entry.isFile()).map((entry) => ({ name: entry.name }));
  files.sort((a, b) => a.name.localeCompare(b.name));
  return files;
}
