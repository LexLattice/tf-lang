#!/usr/bin/env node
import { spawn } from 'node:child_process';
import { fileURLToPath } from 'node:url';

const repoRoot = new URL('../..', import.meta.url);
const cliPath = new URL('../../packages/tf-trace/bin/trace.mjs', import.meta.url);

const tasks = [
  ['validate', '--in', 'samples/c/trace_small.jsonl'],
  ['summary', '--in', 'samples/c/trace_small.jsonl', '--out', 'out/0.5/trace/summary.json'],
  ['budget', '--in', 'samples/c/trace_small.jsonl', '--spec', 'tf/blocks/C-Trace-Perf/budgets.sample.json'],
  ['export', '--in', 'samples/c/trace_small.jsonl', '--csv', 'out/0.5/trace/trace.csv'],
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
