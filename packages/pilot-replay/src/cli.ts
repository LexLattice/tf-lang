#!/usr/bin/env node
import { replay, writeFramesNdjson } from './index.js';

function main(argv: string[]): void {
  const [command, ...rest] = argv;
  if (command !== 'replay') {
    throw new Error('Usage: pilot-replay replay --input <file> --seed <seed> [--slice start:end:step] --out <file>');
  }
  const options = parseArgs(rest);
  const result = replay(options);
  writeFramesNdjson(options.out, result.frames);
}

interface CliOptions {
  input: string;
  seed: number;
  slice?: string;
  out: string;
}

function parseArgs(args: string[]): CliOptions {
  const options: Partial<CliOptions> = {};
  for (let i = 0; i < args.length; i += 1) {
    const arg = args[i];
    switch (arg) {
      case '--input':
        options.input = args[++i];
        break;
      case '--seed':
        options.seed = Number(args[++i]);
        break;
      case '--slice':
        options.slice = args[++i];
        break;
      case '--out':
        options.out = args[++i];
        break;
      default:
        throw new Error(`Unknown argument: ${arg}`);
    }
  }
  if (!options.input || !options.out || options.seed === undefined) {
    throw new Error('Missing required arguments');
  }
  if (!Number.isFinite(options.seed)) {
    throw new Error('Seed must be a finite number');
  }
  return options as CliOptions;
}

if (import.meta.url === `file://${process.argv[1]}`) {
  main(process.argv.slice(2));
}
