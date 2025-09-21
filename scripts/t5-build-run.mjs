#!/usr/bin/env node
import { mkdir, writeFile, rm } from 'node:fs/promises';
import { join, dirname } from 'node:path';
import { fileURLToPath } from 'node:url';

import {
  DEFAULT_INPUT,
  DEFAULT_SLICE,
  DEFAULT_SEED,
  loadReplayFrames,
  runStrategyOrders,
  evaluateRiskMetrics,
  computeFills,
  computeLedgerState,
  collectPilotOutputs,
  toNdjson,
  toJson,
} from './lib/pilot-full-support.mjs';

const here = dirname(fileURLToPath(import.meta.url));
const rootDir = join(here, '..');
const outDir = join(rootDir, 'out', 't5-full');

async function main() {
  if (process.env.TF_PILOT_FULL !== '1') {
    console.log('t5-build-run: TF_PILOT_FULL not set, skipping');
    return;
  }

  await rm(outDir, { recursive: true, force: true });
  await mkdir(outDir, { recursive: true });

  const seed = DEFAULT_SEED;
  const frames = loadReplayFrames({ input: DEFAULT_INPUT, slice: DEFAULT_SLICE, seed });
  const momentumOrders = runStrategyOrders(frames, seed, 'momentum');
  const meanReversionOrders = runStrategyOrders(frames, seed, 'mean-reversion');
  const riskMetrics = evaluateRiskMetrics([...momentumOrders, ...meanReversionOrders], frames, 'exposure');
  const fills = computeFills([...momentumOrders, ...meanReversionOrders], frames);
  const state = computeLedgerState(fills, seed);

  const outputs = collectPilotOutputs({ frames, momentumOrders, meanReversionOrders, riskMetrics, fills, state });

  await writeFile(join(outDir, 'frames.ndjson'), toNdjson(outputs.frames));
  await writeFile(join(outDir, 'orders.ndjson'), toNdjson(outputs.orders));
  await writeFile(join(outDir, 'fills.ndjson'), toNdjson(outputs.fills));
  await writeFile(join(outDir, 'state.json'), toJson(outputs.state));

  console.log('t5-build-run: completed artifacts in', outDir);
}

main().catch((err) => {
  console.error(err?.stack || err?.message || String(err));
  process.exitCode = 1;
});
