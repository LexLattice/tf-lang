#!/usr/bin/env node
import { Command } from 'commander';
import { resolve } from 'node:path';
import {
  parseNumberOption,
  runEnumerateCommand,
  runExportCommand,
  runScoreCommand,
} from './index.js';

const program = new Command();
program
  .name('tf-plan')
  .description('tf-plan branch enumeration and scoring toolkit');

program
  .command('enumerate')
  .requiredOption('--spec <path>', 'Path to the tf-spec JSON file')
  .option('--seed <number>', 'Random seed for deterministic enumeration', '42')
  .option('--beam <number>', 'Beam width per component')
  .option('--beam-width <number>', 'Alias of --beam')
  .option('--max <number>', 'Maximum branch nodes to keep')
  .option('--out <dir>', 'Output directory for plan artifacts', 'out/t4/plan')
  .action(async (options) => {
    try {
      const beamRaw = options.beam ?? options.beamWidth;
      const plan = await runEnumerateCommand({
        specPath: resolve(options.spec),
        seed: parseNumberOption(options.seed, 42),
        beamWidth: beamRaw ? parseNumberOption(beamRaw, 0) : undefined,
        maxBranches: options.max ? parseNumberOption(options.max, 0) : undefined,
        outDir: resolve(options.out),
      });
      if (!plan) {
        process.exitCode = 1;
      }
    } catch (error) {
      console.error((error as Error).message);
      process.exitCode = 1;
    }
  });

program
  .command('score')
  .requiredOption('--plan <path>', 'Path to plan.json')
  .option('--seed <number>', 'Override seed when re-scoring')
  .option('--out <path>', 'Output path for scored plan', 'out/t4/plan/plan.scored.json')
  .action(async (options) => {
    try {
      await runScoreCommand({
        planPath: resolve(options.plan),
        seed: options.seed ? parseNumberOption(options.seed, 42) : undefined,
        outPath: resolve(options.out),
      });
    } catch (error) {
      console.error((error as Error).message);
      process.exitCode = 1;
    }
  });

program
  .command('export')
  .requiredOption('--plan <path>', 'Path to plan.json')
  .option('--ndjson <path>', 'Output NDJSON path', 'out/t4/plan/plan.ndjson')
  .action(async (options) => {
    try {
      await runExportCommand({
        planPath: resolve(options.plan),
        ndjsonPath: resolve(options.ndjson),
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
