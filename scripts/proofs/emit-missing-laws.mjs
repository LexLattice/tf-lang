#!/usr/bin/env node
import { readFile, writeFile, mkdir } from 'node:fs/promises';
import { dirname, resolve } from 'node:path';
import process from 'node:process';

import { analyzeCoverage } from './coverage.mjs';

const COVERAGE_PATH = 'out/0.4/proofs/coverage.json';
const STUB_DIR = 'out/0.4/proofs/laws/stubs';

async function main() {
  const coverage = await loadCoverage();
  const missing = Array.isArray(coverage?.missing_laws_for_used)
    ? coverage.missing_laws_for_used
    : [];

  if (missing.length === 0) {
    process.stdout.write('no missing commutation laws detected\n');
    return;
  }

  for (const [left, right] of missing) {
    const fileName = `commute_${sanitize(left)}_${sanitize(right)}.smt2`;
    const filePath = resolve(STUB_DIR, fileName);
    const contents = buildStub(left, right);
    await mkdir(dirname(filePath), { recursive: true });
    await writeFile(filePath, ensureTrailingNewline(contents), 'utf8');
    process.stdout.write(`wrote ${filePath}\n`);
  }
}

async function loadCoverage() {
  try {
    const raw = await readFile(COVERAGE_PATH, 'utf8');
    return JSON.parse(raw);
  } catch (error) {
    if (error && error.code === 'ENOENT') {
      const { coverage } = await analyzeCoverage();
      return coverage;
    }
    throw error;
  }
}

function buildStub(left, right) {
  const header = `; stub: ${left} ↔ ${right}`;
  return [
    header,
    '(declare-sort Val 0)',
    '(declare-fun A (Val) Val)',
    '(declare-fun B (Val) Val)',
    '(assert (forall ((x Val)) (= (A (B x)) (B (A x)))))',
    '(declare-const x Val)',
    '(define-fun seqAB () Val (A (B x)))',
    '(define-fun seqBA () Val (B (A x)))',
    '(assert (not (= seqAB seqBA)))',
    '(check-sat)'
  ].join('\n');
}

function sanitize(value) {
  return value.replace(/[^A-Za-z0-9]+/g, '_');
}

function ensureTrailingNewline(text) {
  return text.endsWith('\n') ? text : `${text}\n`;
}

main().catch((error) => {
  process.stderr.write(`${error.message}\n`);
  process.exit(1);
});

