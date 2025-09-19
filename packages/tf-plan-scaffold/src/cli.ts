#!/usr/bin/env node
import { Command } from 'commander';
import { resolve } from 'node:path';
import { applyScaffold, generateScaffold, parseNumber, parseTemplate } from './index.js';

const program = new Command();
program
  .name('tf-plan-scaffold')
  .description('tf-plan scaffolding utilities');

program
  .command('scaffold')
  .option('--plan <path>', 'Path to plan.ndjson', 'out/t4/plan/plan.ndjson')
  .option('--graph <path>', 'Optional plan.json metadata path')
  .option('--top <number>', 'Number of branches to scaffold', '3')
  .option('--template <kind>', 'Template kind (ts|rs|dual-stack)', 'dual-stack')
  .option('--out <path>', 'Output index JSON path', 'out/t4/scaffold/index.json')
  .option('--base <branch>', 'Base branch name', 'main')
  .option('--apply <path>', 'Apply an existing scaffold index instead of generating')
  .action(async (options) => {
    try {
      if (options.apply) {
        await applyScaffold({ indexPath: resolve(options.apply) });
        return;
      }
      await generateScaffold({
        planNdjsonPath: resolve(options.plan),
        planJsonPath: options.graph ? resolve(options.graph) : undefined,
        top: parseNumber(options.top, 3),
        template: parseTemplate(options.template, 'dual-stack'),
        outPath: resolve(options.out),
        baseBranch: options.base,
      });
    } catch (error) {
      console.error((error as Error).message);
      process.exitCode = 1;
    }
  });

program
  .command('pr')
  .option('--apply <path>', 'Path to scaffold index JSON')
  .option('--open-draft', 'Open a draft PR via gh cli')
  .action(() => {
    console.log('Draft PR automation is not implemented. Use the scaffold index to prepare branches manually.');
  });

program.parseAsync(process.argv).catch((error) => {
  console.error((error as Error).message);
  process.exitCode = 1;
});
