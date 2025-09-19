#!/usr/bin/env node
import { resolve } from 'node:path';
import { fileURLToPath } from 'node:url';

import { replay, writeFramesNdjson } from './index.js';

function main(argv: string[]): void {
  if (argv.includes('--help')) {
    printHelp();
    return;
  }
  const [command, ...rest] = argv;
  if (command !== 'replay') {
    printHelp();
    throw new Error('Unknown command');
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
    printHelp();
    throw new Error('Missing required arguments');
  }
  if (!Number.isFinite(options.seed)) {
    throw new Error('Seed must be a finite number');
  }
  return options as CliOptions;
}

function printHelp(): void {
  const lines = [
    'Usage: pilot-replay replay --input <file> --seed <seed> [--slice start:end:step] --out <file>',
    '',
    'Options:',
    '  --input   Path to the CSV tick data.',
    '  --seed    Deterministic seed forwarded to downstream components.',
    '  --slice   Optional slicing directive start:end:step.',
    '  --out     Output path for canonical frames.ndjson.',
  ];
  console.log(lines.join('\n'));
}

const entrypoint = fileURLToPath(import.meta.url);
const executed = process.argv[1] ? resolve(process.argv[1]) : '';
if (entrypoint === executed) {
  main(process.argv.slice(2));
}
