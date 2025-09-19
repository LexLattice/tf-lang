#!/usr/bin/env node
import { readFramesNdjson, runStrategy, writeOrdersNdjson } from './index.js';

function main(argv: string[]): void {
  const [command, ...rest] = argv;
  if (command !== 'run') {
    throw new Error('Usage: pilot-strategy run --strategy <name> --frames <file> --seed <seed> --out <file>');
  }
  const options = parseArgs(rest);
  const frames = readFramesNdjson(options.frames);
  const result = runStrategy({ strategy: options.strategy, framesPath: options.frames, seed: options.seed }, frames);
  writeOrdersNdjson(options.out, result.orders);
}

interface CliOptions {
  strategy: 'momentum' | 'meanReversion';
  frames: string;
  seed: number;
  out: string;
}

function parseArgs(args: string[]): CliOptions {
  const options: Partial<CliOptions> = {};
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
  return options as CliOptions;
}

if (import.meta.url === `file://${process.argv[1]}`) {
  main(process.argv.slice(2));
}
