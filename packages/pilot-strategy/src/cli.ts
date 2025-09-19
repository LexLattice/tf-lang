#!/usr/bin/env node
import { fileURLToPath } from 'node:url';
import { resolve } from 'node:path';

import { readFramesNdjson, runStrategy, writeOrdersNdjson, StrategyDefaults } from './index.js';

function main(argv: string[]): void {
  const [command, ...rest] = argv;
  if (!command || command === '--help' || command === 'help') {
    printUsage();
    return;
  }
  if (command !== 'run') {
    printUsage(true);
    return;
  }
  const options = parseArgs(rest);
  const frames = readFramesNdjson(options.frames);
  const result = runStrategy(
    {
      strategy: options.strategy,
      framesPath: options.frames,
      seed: options.seed,
      overrides: options.overrides,
    },
    frames,
  );
  writeOrdersNdjson(options.out, result.orders);
}

interface CliOptions {
  strategy: 'momentum' | 'meanReversion';
  frames: string;
  seed: number;
  out: string;
  overrides?: {
    window?: number;
    delta?: number;
    quantity?: string;
  };
}

function parseArgs(args: string[]): CliOptions {
  const options: Partial<CliOptions> = { overrides: {} };
  for (let i = 0; i < args.length; i += 1) {
    const arg = args[i];
    switch (arg) {
      case '--strategy':
        options.strategy = args[++i] as CliOptions['strategy'];
        break;
      case '--frames':
        options.frames = args[++i];
        break;
      case '--seed':
        options.seed = Number(args[++i]);
        break;
      case '--out':
        options.out = args[++i];
        break;
      case '--window':
        options.overrides = options.overrides ?? {};
        options.overrides.window = Number(args[++i]);
        break;
      case '--delta':
        options.overrides = options.overrides ?? {};
        options.overrides.delta = Number(args[++i]);
        break;
      case '--quantity':
        options.overrides = options.overrides ?? {};
        options.overrides.quantity = args[++i];
        break;
      case '--help':
        printUsage();
        process.exit(0);
      default:
        throw new Error(`Unknown argument: ${arg}`);
    }
  }
  if (!options.strategy || !options.frames || options.seed === undefined || !options.out) {
    throw new Error('Missing required arguments');
  }
  if (options.strategy !== 'momentum' && options.strategy !== 'meanReversion') {
    throw new Error(`Unsupported strategy: ${options.strategy}`);
  }
  if (!Number.isFinite(options.seed)) {
    throw new Error('Seed must be finite');
  }
  if (options.overrides?.window !== undefined && !Number.isFinite(options.overrides.window)) {
    throw new Error('Window override must be finite');
  }
  if (options.overrides?.delta !== undefined && !Number.isFinite(options.overrides.delta)) {
    throw new Error('Delta override must be finite');
  }
  return options as CliOptions;
}

function printUsage(error = false): void {
  const lines = [
    'Usage: pilot-strategy run --strategy <momentum|meanReversion> --frames <file> --seed <seed> --out <file> [options]',
    '',
    'Options:',
    '  --window <n>      Override breakout/lookback window length',
    '  --delta <n>       Override mean reversion delta (meanReversion only)',
    '  --quantity <q>    Override order quantity (canonical numeric string)',
    '',
    'Defaults:',
    `  momentum: window=${StrategyDefaults.momentum.breakoutWindow}, quantity=${StrategyDefaults.momentum.quantity}`,
    `  meanReversion: window=${StrategyDefaults.meanReversion.lookbackWindow}, delta=${StrategyDefaults.meanReversion.delta}, quantity=${StrategyDefaults.meanReversion.quantity}`,
  ];
  const stream = error ? process.stderr : process.stdout;
  stream.write(lines.join('\n') + '\n');
}

const entryPath = fileURLToPath(import.meta.url);
const invokedPath = process.argv[1] ? resolve(process.argv[1]) : '';

if (entryPath === invokedPath) {
  main(process.argv.slice(2));
}
