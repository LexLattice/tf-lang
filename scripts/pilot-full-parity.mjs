#!/usr/bin/env node
import { mkdir, writeFile } from 'node:fs/promises';
import { join, dirname } from 'node:path';
import { fileURLToPath } from 'node:url';

import { hashJsonLike } from './hash-jsonl.mjs';

const here = dirname(fileURLToPath(import.meta.url));
const rootDir = join(here, '..');
const generatedDir = join(rootDir, 'out', '0.4', 'pilot-full');
const t5Dir = join(rootDir, 'out', 't5-full');
const reportDir = join(rootDir, 'out', '0.4', 'parity', 'full');
const reportPath = join(reportDir, 'report.json');

async function ensureReportDir() {
  await mkdir(reportDir, { recursive: true });
}

async function computeHashes(baseDir) {
  const artifacts = {
    frames: join(baseDir, 'frames.ndjson'),
    orders: join(baseDir, 'orders.ndjson'),
    fills: join(baseDir, 'fills.ndjson'),
    state: join(baseDir, 'state.json'),
  };
  const hashes = {};
  for (const [key, filePath] of Object.entries(artifacts)) {
    hashes[key] = await hashJsonLike(filePath);
  }
  return hashes;
}

function diffHashes(gen, t5) {
  const diff = [];
  for (const key of Object.keys(gen).sort()) {
    if (gen[key] !== t5[key]) {
      diff.push({ artifact: key, generated: gen[key], t5: t5[key] });
    }
  }
  return diff;
}

async function main() {
  await ensureReportDir();
  const generated = await computeHashes(generatedDir);
  const t5 = await computeHashes(t5Dir);
  const diff = diffHashes(generated, t5);
  const report = {
    equal: diff.length === 0,
    diff,
    generated,
    t5,
  };
  await writeFile(reportPath, JSON.stringify(report, null, 2) + '\n');
  if (!report.equal) {
    console.warn('pilot-full-parity: mismatch detected');
    process.exitCode = 1;
  } else {
    console.log('pilot-full-parity: artifacts match');
  }
}

main().catch((err) => {
  console.error(err?.stack || err?.message || String(err));
  process.exitCode = 1;
});
