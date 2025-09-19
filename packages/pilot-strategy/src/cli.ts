#!/usr/bin/env node
import { resolve } from 'node:path';
import { fileURLToPath } from 'node:url';

import {
  STRATEGY_DEFAULTS,
  StrategyName,
  StrategyParams,
  readFramesNdjson,
  runStrategy,
  writeOrdersNdjson,
} from './index.js';

interface CliOptions {
  strategy: StrategyName;
  frames: string;
  seed: number;
  out: string;
  overrides: Partial<Record<StrategyName, Partial<StrategyParams[StrategyName]>>>;
}

function main(argv: string[]): void {
  if (argv.includes('--help') || argv.includes('-h')) {
    printHelp();
    return;
  }
  const filtered = argv.filter((arg) => arg !== '--help' && arg !== '-h');
  const [command, ...rest] = filtered;
  if (command !== 'run') {
    throw new Error('Usage: pilot-strategy run --strategy <name> --frames <file> --seed <seed> --out <file>');
  }
  const options = parseArgs(rest);
  const frames = readFramesNdjson(options.frames);
  const result = runStrategy(
    {
      strategy: options.strategy,
      framesPath: options.frames,
      seed: options.seed,
      params: options.overrides[options.strategy],
    },
    frames,
  );
  writeOrdersNdjson(options.out, result.orders);
}

function parseArgs(args: string[]): CliOptions {
  const options: Partial<CliOptions> = { overrides: {} };
  for (let i = 0; i < args.length; i += 1) {
    const arg = args[i];
    if (arg.startsWith('--') && arg.includes('.')) {
      const key = arg.slice(2);
      const [strategyKey, field] = key.split('.', 2);
      if (!isStrategyName(strategyKey)) {
        throw new Error(`Unknown strategy override: ${arg}`);
      }
      const defaults = STRATEGY_DEFAULTS[strategyKey];
      if (!(field in defaults)) {
        throw new Error(`Unknown strategy override field: ${arg}`);
      }
      const next = args[++i];
      if (next === undefined) {
        throw new Error(`Missing value for ${arg}`);
      }
      const value = coerceOverrideValue(defaults[field as keyof typeof defaults], next);
      if (!options.overrides) {
        options.overrides = {};
      }
      if (!options.overrides[strategyKey]) {
        options.overrides[strategyKey] = {};
      }
      (options.overrides[strategyKey] as Record<string, unknown>)[field] = value;
      continue;
    }
    switch (arg) {
      case '--strategy': {
        const value = args[++i];
        if (!value) {
          throw new Error('Missing strategy name');
        }
        if (!isStrategyName(value)) {
          throw new Error(`Unsupported strategy: ${value}`);
        }
        options.strategy = value;
        break;
      }
      case '--frames':
        options.frames = args[++i];
        break;
      case '--seed': {
        const raw = args[++i];
        const seed = Number(raw);
        if (!Number.isFinite(seed)) {
          throw new Error('Seed must be finite');
        }
        options.seed = seed;
        break;
      }
      case '--out':
        options.out = args[++i];
        break;
      default:
        throw new Error(`Unknown argument: ${arg}`);
    }
  }
  if (!options.strategy || !options.frames || options.seed === undefined || !options.out) {
    throw new Error('Missing required arguments');
  }
  return options as CliOptions;
}

function coerceOverrideValue(defaultValue: unknown, raw: string): unknown {
  if (typeof defaultValue === 'number') {
    const numeric = Number(raw);
    if (!Number.isFinite(numeric)) {
      throw new Error(`Override expects a numeric value: ${raw}`);
    }
    return numeric;
  }
  return raw;
}

function isStrategyName(value: string): value is StrategyName {
  return value === 'momentum' || value === 'meanReversion';
}

function printHelp(): void {
  const defaults = JSON.stringify(STRATEGY_DEFAULTS, null, 2);
  console.log(`Usage: pilot-strategy run --strategy <name> --frames <file> --seed <seed> --out <file>\n\n` +
    `Override defaults per strategy using flags such as --momentum.window 5 or --meanReversion.delta 0.2.\n\n` +
    `Current defaults:\n${defaults}`);
}

const entryPath = fileURLToPath(import.meta.url);
if (process.argv[1] && entryPath === resolve(process.argv[1])) {
  main(process.argv.slice(2));
}
