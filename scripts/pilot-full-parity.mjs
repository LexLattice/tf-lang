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

const targets = [
  { name: 'frames', file: 'frames.ndjson' },
  { name: 'orders', file: 'orders.ndjson' },
  { name: 'fills', file: 'fills.ndjson' },
  { name: 'state', file: 'state.json' },
];

async function computeHashes() {
  const report = { equal: true, diff: [], generated: {}, t5: {} };
  for (const target of targets) {
    const generatedPath = join(generatedDir, target.file);
    const t5Path = join(t5Dir, target.file);
    const generatedHash = await hashJsonLike(generatedPath);
    const t5Hash = await hashJsonLike(t5Path);
    report.generated[target.name] = generatedHash;
    report.t5[target.name] = t5Hash;
    if (generatedHash !== t5Hash) {
      report.equal = false;
      report.diff.push({ artifact: target.name, generated: generatedHash, t5: t5Hash });
    }
  }
  return report;
}

async function main() {
  await mkdir(reportDir, { recursive: true });
  const report = await computeHashes();
  await writeFile(reportPath, JSON.stringify(report, null, 2) + '\n');
  if (report.equal) {
    console.log('pilot-full-parity: artifacts match');
  } else {
    console.warn('pilot-full-parity: mismatch detected');
    process.exitCode = 1;
  }
}

main().catch((err) => {
  console.error(err?.stack || err?.message || String(err));
  process.exitCode = 1;
});
