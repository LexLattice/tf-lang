#!/usr/bin/env node
import { performance } from 'node:perf_hooks';
import { mkdirSync, writeFileSync } from 'node:fs';
import path from 'node:path';

import { runWorkload } from '../dist/bench/workload.js';

const ITERATIONS = Number(process.env.ITER ?? 10000);
const RUNS = Number(process.env.RUNS ?? 7);

function timeOnce() {
  const start = performance.now();
  runWorkload(ITERATIONS);
  return performance.now() - start;
}

const samples = Array.from({ length: RUNS }, () => timeOnce());
const mean = samples.reduce((acc, value) => acc + value, 0) / samples.length;
const variance = samples.reduce((acc, value) => acc + (value - mean) ** 2, 0) / samples.length;
const stdev = Math.sqrt(variance);

const mode = process.env.DEV_PROOFS === '1' ? 'on' : 'off';
const result = { mode, iter: ITERATIONS, runs: RUNS, samples, mean, stdev };

const outDir = path.resolve('out/t3/perf');
mkdirSync(outDir, { recursive: true });
const outputPath = path.join(outDir, `dev_proofs_${mode}.json`);
writeFileSync(outputPath, JSON.stringify(result, null, 2), 'utf8');
process.stdout.write(`${JSON.stringify(result)}\n`);
