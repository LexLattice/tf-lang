#!/usr/bin/env node
import { readFile } from 'node:fs/promises';
import { resolve } from 'node:path';
import process from 'node:process';

import { run } from '../dist/index.js';

function printUsage() {
  console.log(
    [
      'Usage: tf-run-wasm --ir <file.ir.json> [options]',
      '',
      'Options:',
      '  --status <file.json>   Write the status JSON document to disk',
      '  --trace <file.jsonl>   Write the trace JSONL document to disk',
      '  --help                 Show this message',
    ].join('\n'),
  );
}

function takeValue(argv, index, flag) {
  const next = argv[index + 1];
  if (typeof next !== 'string' || next.length === 0 || next.startsWith('-')) {
    throw new Error(`Expected a value after ${flag}`);
  }
  return next;
}

function parseArgs(argv) {
  const options = {
    help: false,
    irPath: null,
    statusPath: null,
    tracePath: null,
  };

  for (let i = 0; i < argv.length; i += 1) {
    const arg = argv[i];
    switch (arg) {
      case '--help':
      case '-h':
        options.help = true;
        return options;
      case '--ir':
        options.irPath = takeValue(argv, i, '--ir');
        i += 1;
        break;
      case '--status':
        options.statusPath = takeValue(argv, i, '--status');
        i += 1;
        break;
      case '--trace':
        options.tracePath = takeValue(argv, i, '--trace');
        i += 1;
        break;
      default:
        if (arg.startsWith('-')) {
          throw new Error(`Unknown argument: ${arg}`);
        }
        throw new Error(`Unexpected positional argument: ${arg}`);
    }
  }

  return options;
}

async function main(argv) {
  let options;
  try {
    options = parseArgs(argv);
  } catch (err) {
    const message = err instanceof Error && typeof err.message === 'string' ? err.message : String(err);
    console.error(`Error: ${message}`);
    printUsage();
    process.exitCode = 1;
    return;
  }

  if (options.help) {
    printUsage();
    return;
  }

  if (!options.irPath) {
    console.error('Error: Expected --ir <file.ir.json>');
    printUsage();
    process.exitCode = 1;
    return;
  }

  try {
    const irPath = resolve(options.irPath);
    const irSource = await readFile(irPath, 'utf8');

    await run({
      irSource,
      statusPath: options.statusPath ? resolve(options.statusPath) : undefined,
      tracePath: options.tracePath ? resolve(options.tracePath) : undefined,
    });
  } catch (err) {
    const message = err instanceof Error && typeof err.message === 'string' ? err.message : String(err);
    console.error(`Runtime error: ${message}`);
    process.exitCode = 1;
  }
}

await main(process.argv.slice(2));
