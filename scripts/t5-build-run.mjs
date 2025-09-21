#!/usr/bin/env node
import { mkdir, rm, writeFile } from 'node:fs/promises';
import { join, dirname } from 'node:path';
import { fileURLToPath } from 'node:url';

import { summariseFile } from '../packages/pilot-core/dist/index.js';

import {
  computeState,
  evaluateRisk,
  replayFrames,
  resolveConfig,
  runStrategies,
  simulateFills,
  toNdjson,
} from './lib/pilot-full-helpers.mjs';
import { canonicalStringify, hashJsonLike } from './hash-jsonl.mjs';

const here = dirname(fileURLToPath(import.meta.url));
const rootDir = join(here, '..');
const outDir = join(rootDir, 'out', 't5-full');

async function removeIfExists(path) {
  await rm(path, { recursive: true, force: true });
}

async function ensureDir(path) {
  await mkdir(path, { recursive: true });
}

async function writeText(path, content) {
  await writeFile(path, content, 'utf8');
}

async function main() {
  await ensureDir(outDir);

  const framesPath = join(outDir, 'frames.ndjson');
  const ordersPath = join(outDir, 'orders.ndjson');
  const metricsPath = join(outDir, 'metrics.ndjson');
  const fillsPath = join(outDir, 'fills.ndjson');
  const statePath = join(outDir, 'state.json');
  const summaryPath = join(outDir, 'summary.json');
  const digestsPath = join(outDir, 'digests.json');

  await Promise.all([
    removeIfExists(framesPath),
    removeIfExists(ordersPath),
    removeIfExists(metricsPath),
    removeIfExists(fillsPath),
    removeIfExists(statePath),
    removeIfExists(summaryPath),
    removeIfExists(digestsPath),
  ]);

  const config = resolveConfig({ seed: 42, slice: '0:50:1' });
  const frames = replayFrames(config);
  const orders = runStrategies(config, frames);
  const metrics = evaluateRisk(config, orders, frames);
  const fills = simulateFills(orders, frames);
  const state = computeState(config, fills);

  await writeText(framesPath, toNdjson(frames));
  await writeText(ordersPath, toNdjson(orders));
  await writeText(metricsPath, toNdjson(metrics));
  await writeText(fillsPath, toNdjson(fills));
  await writeText(statePath, JSON.stringify(state, null, 2) + '\n');

  const artifactsSummary = {
    frames: summariseFile(framesPath),
    orders: summariseFile(ordersPath),
    fills: summariseFile(fillsPath),
    metrics: summariseFile(metricsPath),
    state: summariseFile(statePath),
  };

  await writeText(summaryPath, canonicalStringify({ artifacts: artifactsSummary }) + '\n');

  const digests = {
    frames: await hashJsonLike(framesPath),
    orders: await hashJsonLike(ordersPath),
    fills: await hashJsonLike(fillsPath),
    metrics: await hashJsonLike(metricsPath),
    state: await hashJsonLike(statePath),
    summary: await hashJsonLike(summaryPath),
  };
  await writeText(digestsPath, JSON.stringify(digests, null, 2) + '\n');

  console.log('t5-build-run: completed artifacts in', outDir);
}

main().catch((err) => {
  console.error(err?.stack || err?.message || String(err));
  process.exitCode = 1;
});
