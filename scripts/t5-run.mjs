#!/usr/bin/env node
import { spawnSync } from 'node:child_process';
import { fileURLToPath } from 'node:url';
import { dirname, resolve } from 'node:path';

const argv = process.argv.slice(2);
const FORCE = argv.includes('--force');

function run(cmd, args) {
  const { status } = spawnSync(cmd, args, { stdio: 'inherit' });
  if (status !== 0) process.exit(status ?? 1);
}

const base = [
  ['node','packages/pilot-replay/dist/cli.js','replay',
    '--input','tests/data/ticks-mini.csv','--seed','42','--slice','0:50:1',
    '--out','out/t5/replay/frames.ndjson'],
  ['node','packages/pilot-strategy/dist/cli.js','run',
    '--strategy','momentum','--frames','out/t5/replay/frames.ndjson',
    '--seed','42','--out','out/t5/effects/orders.ndjson'],
  ['node','packages/pilot-risk/dist/index.js','eval',
    '--orders','out/t5/effects/orders.ndjson',
    '--frames','out/t5/replay/frames.ndjson',
    '--out','out/t5/risk/evaluations.ndjson'],
];

// Propagate --force to CLIs that support it
for (const step of base) {
  const [cmd, ...args] = step;
  const finalArgs = FORCE ? [...args, '--force'] : args;
  run(cmd, finalArgs);
}

// Status writer last (no --force needed)
run('node', ['scripts/t5-write-status.js']);
