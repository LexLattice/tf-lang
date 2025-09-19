#!/usr/bin/env node
import { resolve } from 'node:path';
import { fileURLToPath } from 'node:url';

import { parseCommonFlags } from '@tf-lang/pilot-core';

import { replay, writeFramesNdjson } from './index.js';

interface ReplayCliOptions {
  input: string;
}

export function runCli(argv: string[]): number {
  try {
    const [command, ...rest] = argv;
    if (command !== 'replay') {
      throw new Error('Usage: pilot-replay replay --input <file> --seed <seed> [--slice start:end:step] --out <file>');
    }
    const common = parseCommonFlags(rest, { requireSeed: true, requireOut: true });
    const specific = parseReplayArgs(common.rest);
    if (!common.outPath) {
      throw new Error('Missing required --out flag');
    }
    const result = replay({
      input: specific.input,
      seed: common.seed,
      slice: common.slice,
    });
    writeFramesNdjson(common.outPath, result.frames);
    return 0;
  } catch (error) {
    console.error((error as Error).message);
    return 1;
  }
}

function parseReplayArgs(args: string[]): ReplayCliOptions {
  const options: Partial<ReplayCliOptions> = {};
  for (let i = 0; i < args.length; i += 1) {
    const arg = args[i];
    switch (arg) {
      case '--input':
        options.input = args[++i];
        break;
      default:
        throw new Error(`Unknown argument: ${arg}`);
    }
  }
  if (!options.input) {
    throw new Error('Missing required --input flag');
  }
  return options as ReplayCliOptions;
}

function main(argv: string[]): void {
  const code = runCli(argv);
  if (code !== 0) {
    process.exitCode = code;
  }
}

const entryPath = fileURLToPath(import.meta.url);
if (process.argv[1] && entryPath === resolve(process.argv[1])) {
  main(process.argv.slice(2));
}
