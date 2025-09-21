#!/usr/bin/env node
import { mkdir, rm, writeFile } from 'node:fs/promises';
import { dirname, join } from 'node:path';
import { fileURLToPath } from 'node:url';

import computePilotFullPipeline from './lib/pilot-full-pipeline.mjs';

const here = dirname(fileURLToPath(import.meta.url));
const rootDir = join(here, '..');
const outDir = join(rootDir, 'out', 't5-full');

async function main() {
  if (process.env.TF_PILOT_FULL !== '1') {
    console.log('t5-build-run: TF_PILOT_FULL != 1, skipping heavy pilot run');
    return;
  }

  const seed = Number(process.env.TF_PILOT_SEED ?? '42');
  const slice = process.env.TF_PILOT_SLICE ?? '0:50:1';
  const inputPath = process.env.TF_PILOT_INPUT ?? join(rootDir, 'tests', 'data', 'ticks-mini.csv');

  await rm(outDir, { recursive: true, force: true });
  await mkdir(outDir, { recursive: true });

  const pipeline = await computePilotFullPipeline({ seed, slice, inputPath });

  await writeFile(join(outDir, 'frames.ndjson'), pipeline.framesNdjson, 'utf8');
  await writeFile(join(outDir, 'orders.ndjson'), pipeline.orders.combinedNdjson, 'utf8');
  await writeFile(join(outDir, 'fills.ndjson'), pipeline.fills.ndjson, 'utf8');
  await writeFile(join(outDir, 'state.json'), pipeline.state.json + '\n', 'utf8');
  await writeFile(join(outDir, 'risk.ndjson'), pipeline.risk.ndjson, 'utf8');

  console.log('t5-build-run: wrote artifacts to', outDir);
}

main().catch((err) => {
  console.error(err?.stack || err?.message || String(err));
  process.exitCode = 1;
});
