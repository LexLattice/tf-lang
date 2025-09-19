#!/usr/bin/env node
import { resolve } from 'node:path';
import { fileURLToPath } from 'node:url';

import {
  STRATEGY_DEFAULTS,
  StrategyName,
  StrategyParameters,
  readFramesNdjson,
  runStrategy,
  writeOrdersNdjson,
} from './index.js';

function main(argv: string[]): void {
  if (argv.includes('--help')) {
    printHelp();
    return;
  }
  const [command, ...rest] = argv;
  if (command !== 'run') {
    printHelp();
    throw new Error('Unknown command');
  }
  const options = parseArgs(rest);
  const frames = readFramesNdjson(options.frames);
  const parameterOverrides = normaliseParameters(options.strategy, options.parameters);
  const result = runStrategy(
    {
      strategy: options.strategy,
      framesPath: options.frames,
      seed: options.seed,
      parameters: parameterOverrides,
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
  parameters: Record<string, string>;
}

function parseArgs(args: string[]): CliOptions {
  const options: Partial<CliOptions> = { parameters: {} };
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
      case '--delta':
      case '--quantity': {
        if (i + 1 >= args.length) {
          throw new Error(`Missing value for ${arg}`);
        }
        options.parameters![arg.slice(2)] = args[++i];
        break;
      }
      case '--help':
        printHelp();
        return process.exit(0) as never;
      default:
        throw new Error(`Unknown argument: ${arg}`);
    }
  }
  if (!options.strategy || !options.frames || options.seed === undefined || !options.out) {
    printHelp();
    throw new Error('Missing required arguments');
  }
  if (options.strategy !== 'momentum' && options.strategy !== 'meanReversion') {
    throw new Error(`Unsupported strategy: ${options.strategy}`);
  }
  if (!Number.isFinite(options.seed)) {
    throw new Error('Seed must be finite');
  }
  return options as CliOptions;
}

function normaliseParameters<Name extends StrategyName>(
  strategy: Name,
  raw: Record<string, string>,
): Partial<StrategyParameters[Name]> {
  if (strategy === 'momentum') {
    const overrides: Partial<StrategyParameters['momentum']> = {};
    if (raw.window !== undefined) {
      const value = Number(raw.window);
      if (!Number.isFinite(value)) {
        throw new Error('Momentum window override must be numeric');
      }
      overrides.window = Math.trunc(value);
    }
    if (raw.quantity !== undefined) {
      overrides.quantity = raw.quantity;
    }
    return overrides as Partial<StrategyParameters[Name]>;
  }
  const overrides: Partial<StrategyParameters['meanReversion']> = {};
  if (raw.window !== undefined) {
    const value = Number(raw.window);
    if (!Number.isFinite(value)) {
      throw new Error('Mean reversion window override must be numeric');
    }
    overrides.window = Math.trunc(value);
  }
  if (raw.delta !== undefined) {
    const value = Number(raw.delta);
    if (!Number.isFinite(value)) {
      throw new Error('Mean reversion delta override must be numeric');
    }
    overrides.delta = value;
  }
  if (raw.quantity !== undefined) {
    overrides.quantity = raw.quantity;
  }
  return overrides as Partial<StrategyParameters[Name]>;
}

function printHelp(): void {
  const defaults = {
    momentum: STRATEGY_DEFAULTS.momentum,
    meanReversion: STRATEGY_DEFAULTS.meanReversion,
  };
  const lines = [
    'Usage: pilot-strategy run --strategy <momentum|meanReversion> --frames <file> --seed <seed> --out <file>',
    '',
    'Optional overrides (per strategy):',
    `  Momentum:      --window <int> [default ${defaults.momentum.window}]  --quantity <value> [default ${defaults.momentum.quantity}]`,
    `  Mean reversion: --window <int> [default ${defaults.meanReversion.window}]  --delta <number> [default ${defaults.meanReversion.delta}]  --quantity <value> [default ${defaults.meanReversion.quantity}]`,
  ];
  console.log(lines.join('\n'));
}

const entrypoint = fileURLToPath(import.meta.url);
const executed = process.argv[1] ? resolve(process.argv[1]) : '';
if (entrypoint === executed) {
  main(process.argv.slice(2));
}
