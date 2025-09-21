#!/usr/bin/env node
import { mkdir, writeFile } from 'node:fs/promises';
import { dirname, join } from 'node:path';
import { fileURLToPath } from 'node:url';

import { hashJsonLike } from './hash-jsonl.mjs';

const here = dirname(fileURLToPath(import.meta.url));
const rootDir = join(here, '..');
const generatedDir = join(rootDir, 'out', '0.4', 'pilot-full');
const t5Dir = join(rootDir, 'out', 't5-full');
const parityDir = join(rootDir, 'out', '0.4', 'parity', 'full');
const reportPath = join(parityDir, 'report.json');

const artifacts = [
  { key: 'frames', file: 'frames.ndjson' },
  { key: 'orders', file: 'orders.ndjson' },
  { key: 'fills', file: 'fills.ndjson' },
  { key: 'state', file: 'state.json' },
];

async function main() {
  await mkdir(parityDir, { recursive: true });

  const report = {
    equal: true,
    diff: [],
    generated: {},
    t5: {},
  };

  for (const artifact of artifacts) {
    const generatedPath = join(generatedDir, artifact.file);
    const t5Path = join(t5Dir, artifact.file);
    const generatedHash = await hashJsonLike(generatedPath);
    const t5Hash = await hashJsonLike(t5Path);
    report.generated[artifact.key] = generatedHash;
    report.t5[artifact.key] = t5Hash;
    if (generatedHash !== t5Hash) {
      report.equal = false;
      report.diff.push({ artifact: artifact.key, generated: generatedHash, t5: t5Hash });
    }
  }

  await writeFile(reportPath, JSON.stringify(report, null, 2) + '\n');
  if (!report.equal) {
    process.exitCode = 1;
  } else {
    console.log('pilot-full-parity: artifacts match');
  }
}

main().catch((err) => {
  console.error(err?.stack || err?.message || String(err));
  process.exitCode = 1;
});
