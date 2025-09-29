#!/usr/bin/env node
import { spawn } from 'node:child_process';
import { fileURLToPath } from 'node:url';

const repoRoot = new URL('../..', import.meta.url);
const cliPath = new URL('../../packages/tf-trace/bin/trace.mjs', import.meta.url);

const argv = process.argv.slice(2);
let traceInput = 'samples/c/trace_small.jsonl';
let budgetSpec = 'samples/c/budgets.sample.json';

for (let i = 0; i < argv.length; i++) {
  const arg = argv[i];
  if (arg === '--in') {
    traceInput = argv[i + 1] ?? traceInput;
    i += 1;
    continue;
  }
  if (arg === '--budgets') {
    budgetSpec = argv[i + 1] ?? budgetSpec;
    i += 1;
  }
}

const tasks = [
  ['validate', '--in', traceInput],
  ['summary', '--in', traceInput, '--out', 'out/0.5/trace/summary.json'],
  ['budget', '--in', traceInput, '--budgets', budgetSpec],
  ['export', '--in', traceInput, '--csv', 'out/0.5/trace/trace.csv'],
  ['export', '--summary', 'out/0.5/trace/summary.json', '--csv', 'out/0.5/trace/summary.csv']
];

async function run() {
  for (const args of tasks) {
    await new Promise((resolve, reject) => {
      const child = spawn('node', [fileURLToPath(cliPath), ...args], {
        cwd: fileURLToPath(repoRoot),
        stdio: 'inherit'
      });
      child.on('close', (code) => {
        if (code === 0) {
          resolve();
        } else {
          reject(new Error(`command failed: ${args.join(' ')}`));
        }
      });
    });
  }
}

run().catch((error) => {
  console.error(error instanceof Error ? error.message : String(error));
  process.exitCode = 1;
});
