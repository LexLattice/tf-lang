#!/usr/bin/env node
import { Command } from 'commander';
import { resolve } from 'node:path';
import { generateComparison } from './index.js';

const program = new Command();
program
  .name('tf-plan-compare')
  .description('tf-plan comparison CLI');

function parseSeed(value: unknown, fallback: number): number {
  if (typeof value === 'number' && Number.isFinite(value)) {
    return value;
  }
  if (typeof value === 'string') {
    const parsed = Number.parseInt(value, 10);
    if (Number.isFinite(parsed)) {
      return parsed;
    }
  }
  return fallback;
}

program
  .command('compare')
  .option('--plan <path>', 'Path to plan.ndjson', 'out/t4/plan/plan.ndjson')
  .option('--inputs <path>', 'Path to scaffold index JSON', 'out/t4/scaffold/index.json')
  .option('--out <dir>', 'Output directory', 'out/t4/compare')
  .option('--seed <number>', 'Seed for comparison ranking', '42')
  .action(async (options) => {
    try {
      await generateComparison({
        planNdjsonPath: resolve(options.plan),
        scaffoldPath: resolve(options.inputs),
        outDir: resolve(options.out),
        seed: parseSeed(options.seed, 42),
      });
    } catch (error) {
      console.error((error as Error).message);
      process.exitCode = 1;
    }
  });

program.parseAsync(process.argv).catch((error) => {
  console.error((error as Error).message);
  process.exitCode = 1;
});
