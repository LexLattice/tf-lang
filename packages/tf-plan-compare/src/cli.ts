#!/usr/bin/env node
import { Command } from 'commander';
import { resolve } from 'node:path';
import { generateComparison } from './index.js';

const program = new Command();
program
  .name('tf-plan-compare')
  .description('tf-plan comparison CLI');

program
  .command('compare')
  .option('--plan <path>', 'Path to plan.ndjson', 'out/t4/plan/plan.ndjson')
  .option('--inputs <path>', 'Path to scaffold index JSON', 'out/t4/scaffold/index.json')
  .option('--out <dir>', 'Output directory', 'out/t4/compare')
  .action(async (options) => {
    try {
      await generateComparison({
        planNdjsonPath: resolve(options.plan),
        scaffoldPath: resolve(options.inputs),
        outDir: resolve(options.out),
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
