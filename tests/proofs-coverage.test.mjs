import test from 'node:test';
import assert from 'node:assert/strict';
import { readFile, rm, stat } from 'node:fs/promises';
import { join, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';
import { execFile } from 'node:child_process';
import { promisify } from 'node:util';

const execFileAsync = promisify(execFile);
const ROOT = resolve(fileURLToPath(new URL('.', import.meta.url)), '..');
const COVERAGE_JSON = resolve(ROOT, 'out/0.4/proofs/coverage.json');
const STUB_DIR = resolve(ROOT, 'out/0.4/proofs/laws/stubs');

const pairKey = (pair) => pair.slice().sort().join('↔');

test('proof coverage tooling', async (t) => {
  await t.test('coverage report is stable', async () => {
    await execFileAsync('node', ['scripts/proofs/coverage.mjs'], { cwd: ROOT });
    const first = JSON.parse(await readFile(COVERAGE_JSON, 'utf8'));
    await execFileAsync('node', ['scripts/proofs/coverage.mjs'], { cwd: ROOT });
    const second = JSON.parse(await readFile(COVERAGE_JSON, 'utf8'));

    assert.deepStrictEqual(second, first);

    const lawKeys = new Set(second.law_backed.map(pairKey));
    assert.ok(lawKeys.has(pairKey(['Pure', 'Observability'])), 'pure↔observability should be backed');

    const missingKeys = new Set(second.missing_laws_for_used.map(pairKey));
    assert.ok(
      missingKeys.has(pairKey(['Observability', 'Network.Out'])),
      'observability↔network.out should be flagged as missing'
    );
  });

  await t.test('stub generation emits files with trailing newline', async () => {
    await rm(STUB_DIR, { recursive: true, force: true });

    const coverage = JSON.parse(await readFile(COVERAGE_JSON, 'utf8'));
    await execFileAsync('node', ['scripts/proofs/emit-missing-laws.mjs'], { cwd: ROOT });

    for (const [left, right] of coverage.missing_laws_for_used) {
      const fileName = `commute_${sanitize(left)}_${sanitize(right)}.smt2`;
      const filePath = join(STUB_DIR, fileName);
      await stat(filePath);
      const contents = await readFile(filePath, 'utf8');
      assert.ok(contents.endsWith('\n'), `stub for ${left}↔${right} should end with newline`);
      const expected =
        [
          `; stub: ${left} ↔ ${right}`,
          '(declare-sort Val 0)',
          '(declare-fun A (Val) Val)',
          '(declare-fun B (Val) Val)',
          '(assert (forall ((x Val)) (= (A (B x)) (B (A x)))))',
          '(declare-const x Val)',
          '(define-fun seqAB () Val (A (B x)))',
          '(define-fun seqBA () Val (B (A x)))',
          '(assert (not (= seqAB seqBA)))',
          '(check-sat)',
          ''
        ].join('\n');
      assert.equal(contents, expected);
    }
  });
});

function sanitize(value) {
  return value.replace(/[^A-Za-z0-9]+/g, '_');
}

