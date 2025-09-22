// @tf-test kind=infra area=proofs speed=medium deps=node

import test from 'node:test';
import assert from 'node:assert/strict';
import { spawnSync } from 'node:child_process';
import { readFile, readdir, mkdir, rm } from 'node:fs/promises';
import path from 'node:path';

const COVERAGE_SCRIPT = ['scripts/proofs/coverage.mjs'];
const EMITTER_SCRIPT = ['scripts/proofs/emit-missing-laws.mjs'];
const OUT_DIR = 'out/0.4/proofs-test';
const COVERAGE_JSON = path.join(OUT_DIR, 'coverage.json');
const COVERAGE_MD = path.join(OUT_DIR, 'coverage.md');
const STUBS_DIR = path.join(OUT_DIR, 'laws/stubs');
const DOCS_PATH = 'out/0.4/proofs-coverage-docs-test.md';

test('proof coverage artifacts are deterministic and stubs are normalized', async () => {
  await rm(OUT_DIR, { recursive: true, force: true });
  await rm(DOCS_PATH, { force: true });
  await mkdir(OUT_DIR, { recursive: true });

  const runCoverage = (...extraArgs) =>
    spawnSync('node', [...COVERAGE_SCRIPT, '--out', OUT_DIR, ...extraArgs], { stdio: 'inherit' });

  const first = runCoverage();
  assert.equal(first.status, 0, 'first coverage run failed');
  const firstJson = await readFile(COVERAGE_JSON, 'utf8');
  const firstMd = await readFile(COVERAGE_MD, 'utf8');

  const second = runCoverage();
  assert.equal(second.status, 0, 'second coverage run failed');
  const secondJson = await readFile(COVERAGE_JSON, 'utf8');
  const secondMd = await readFile(COVERAGE_MD, 'utf8');

  assert.equal(firstJson, secondJson, 'coverage.json should be byte-stable');
  assert.equal(firstJson.endsWith('\n'), true, 'coverage.json should end with a newline');
  assert.equal(firstMd, secondMd, 'coverage.md should be deterministic');

  const emitter = spawnSync('node', [...EMITTER_SCRIPT, '--coverage-json', COVERAGE_JSON], { stdio: 'inherit' });
  assert.equal(emitter.status, 0, 'missing-law emitter failed');

  const files = await readdir(STUBS_DIR);
  assert(files.length > 0, 'expected at least one stub file');
  files.sort();
  for (const file of files) {
    assert.match(file, /^commute_[a-z0-9_]+__[a-z0-9_]+\.smt2$/);
    const content = await readFile(path.join(STUBS_DIR, file), 'utf8');
    assert.equal(content.endsWith('\n'), true, `stub ${file} must end with a newline`);
    assert.notEqual(content.endsWith('\n\n'), true, `stub ${file} must end with exactly one newline`);
  }

  const docRun = runCoverage('--docs', DOCS_PATH);
  assert.equal(docRun.status, 0, '--docs coverage run failed');
  const docContent = await readFile(DOCS_PATH, 'utf8');
  assert.equal(docContent.endsWith('\n'), true, '--docs output should end with newline');

  await rm(OUT_DIR, { recursive: true, force: true });
  await rm(DOCS_PATH, { force: true });
});
