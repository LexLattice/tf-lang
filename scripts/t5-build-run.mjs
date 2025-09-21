#!/usr/bin/env node
import { mkdir, writeFile, rm } from 'node:fs/promises';
import { join, dirname, isAbsolute } from 'node:path';
import { fileURLToPath } from 'node:url';

import { buildPilotArtifacts } from './pilot-full-lib.mjs';
import { hashJsonLike, canonicalStringify } from './hash-jsonl.mjs';

const here = dirname(fileURLToPath(import.meta.url));
const rootDir = join(here, '..');

const seed = Number.isFinite(Number(process.env.TF_PILOT_SEED)) ? Number(process.env.TF_PILOT_SEED) : 42;
const slice = process.env.TF_PILOT_SLICE || '0:50:1';
const inputPath = join(rootDir, 'tests', 'data', 'ticks-mini.csv');

function resolveOutDir() {
  const override = process.env.T5_FULL_OUT_DIR;
  if (override && override.trim()) {
    return isAbsolute(override) ? override : join(rootDir, override);
  }
  return join(rootDir, 'out', 't5-full');
}

const outDir = resolveOutDir();
const replayDir = join(outDir, 'replay');
const strategyDir = join(outDir, 'strategy');
const effectsDir = join(outDir, 'effects');
const riskDir = join(outDir, 'risk');

const framesPath = join(replayDir, 'frames.ndjson');
const momentumPath = join(strategyDir, 'momentum.ndjson');
const meanRevPath = join(strategyDir, 'mean-reversion.ndjson');
const combinedOrdersPath = join(effectsDir, 'orders.ndjson');
const fillsPath = join(effectsDir, 'fills.ndjson');
const statePath = join(outDir, 'state.json');
const digestsPath = join(outDir, 'digests.json');
const riskPath = join(riskDir, 'evaluations.ndjson');

async function ensureDirs() {
  await mkdir(outDir, { recursive: true });
  await mkdir(replayDir, { recursive: true });
  await mkdir(strategyDir, { recursive: true });
  await mkdir(effectsDir, { recursive: true });
  await mkdir(riskDir, { recursive: true });
}

async function removeIfExists(path) {
  await rm(path, { recursive: true, force: true });
}

function toNdjson(records) {
  if (!Array.isArray(records) || records.length === 0) {
    return '';
  }
  return records.map((entry) => JSON.stringify(entry)).join('\n') + '\n';
}

async function main() {
  await ensureDirs();

  await removeIfExists(digestsPath);
  await removeIfExists(fillsPath);
  await removeIfExists(statePath);

  const artifacts = buildPilotArtifacts({ inputPath, seed, slice });

  await writeFile(framesPath, toNdjson(artifacts.frames));
  await writeFile(momentumPath, toNdjson(artifacts.strategies.momentum));
  await writeFile(meanRevPath, toNdjson(artifacts.strategies.meanReversion));
  await writeFile(combinedOrdersPath, toNdjson(artifacts.orders));
  await writeFile(riskPath, toNdjson(artifacts.riskMetrics));
  await writeFile(fillsPath, toNdjson(artifacts.fills));
  await writeFile(statePath, canonicalStringify(artifacts.state) + '\n');

  const digests = {
    frames: await hashJsonLike(framesPath),
    orders: await hashJsonLike(combinedOrdersPath),
    fills: await hashJsonLike(fillsPath),
    state: await hashJsonLike(statePath),
  };
  await writeFile(digestsPath, canonicalStringify(digests) + '\n');

  console.log('t5-build-run: artifacts ready in', outDir);
}

main().catch((err) => {
  console.error(err?.stack || err?.message || String(err));
  process.exitCode = 1;
});
