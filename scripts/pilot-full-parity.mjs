#!/usr/bin/env node
import { mkdir, readFile, writeFile } from 'node:fs/promises';
import { join, dirname, isAbsolute } from 'node:path';
import { fileURLToPath } from 'node:url';

import { canonicalStringify } from './hash-jsonl.mjs';

const here = dirname(fileURLToPath(import.meta.url));
const rootDir = join(here, '..');

function resolveGeneratedDir() {
  const override = process.env.PILOT_FULL_OUT_DIR;
  if (override && override.trim()) {
    return isAbsolute(override) ? override : join(rootDir, override);
  }
  return join(rootDir, 'out', '0.4', 'pilot-full');
}

function resolveT5Dir() {
  const override = process.env.T5_FULL_OUT_DIR;
  if (override && override.trim()) {
    return isAbsolute(override) ? override : join(rootDir, override);
  }
  return join(rootDir, 'out', 't5-full');
}

function resolveParityDir() {
  const override = process.env.PILOT_FULL_PARITY_DIR;
  if (override && override.trim()) {
    return isAbsolute(override) ? override : join(rootDir, override);
  }
  return join(rootDir, 'out', '0.4', 'parity', 'full');
}

async function main() {
  const generatedDir = resolveGeneratedDir();
  const t5Dir = resolveT5Dir();
  const parityDir = resolveParityDir();
  const reportPath = join(parityDir, 'report.json');

  await mkdir(parityDir, { recursive: true });

  const generatedRaw = await readFile(join(generatedDir, 'digests.json'), 'utf8');
  const t5Raw = await readFile(join(t5Dir, 'digests.json'), 'utf8');
  const generated = JSON.parse(generatedRaw);
  const t5 = JSON.parse(t5Raw);

  const keys = Array.from(new Set([...Object.keys(generated), ...Object.keys(t5)])).sort();
  const diff = [];
  let equal = true;

  for (const key of keys) {
    const left = generated[key];
    const right = t5[key];
    if (left !== right) {
      equal = false;
      diff.push({ artifact: key, generated: left ?? null, t5: right ?? null });
    }
  }

  const report = {
    equal,
    diff,
    generated,
    t5,
  };

  await writeFile(reportPath, canonicalStringify(report) + '\n');

  if (!equal) {
    process.exitCode = 1;
    console.warn('pilot-full-parity: mismatch detected, see report at', reportPath);
  } else {
    console.log('pilot-full-parity: artifacts match');
  }
}

main().catch((err) => {
  console.error(err?.stack || err?.message || String(err));
  process.exitCode = 1;
});
