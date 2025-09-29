#!/usr/bin/env node
import { readFile, writeFile, mkdir } from 'node:fs/promises';
import { dirname, resolve } from 'node:path';
import process from 'node:process';

import { run } from '../dist/index.js';

function printUsage() {
  console.log(
    [
      'Usage: tf-run-wasm (--ir <file.ir.json> | --flow <file.tf>) [options]',
      '',
      'Options:',
      '  --json              Print the aggregate JSON result to stdout',
      '  --out <file>        Write the aggregate JSON result to disk',
      '  --status <file>     Write the status JSON document to disk',
      '  --trace <file>      Write the trace JSONL document to disk',
      '  --help              Show this message',
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
    flowPath: null,
    irPath: null,
    outPath: null,
    statusPath: null,
    tracePath: null,
    json: false,
  };
  for (let i = 0; i < argv.length; i += 1) {
    const arg = argv[i];
    switch (arg) {
      case '--help':
      case '-h':
        options.help = true;
        return options;
      case '--flow':
        options.flowPath = takeValue(argv, i, '--flow');
        i += 1;
        break;
      case '--ir':
        options.irPath = takeValue(argv, i, '--ir');
        i += 1;
        break;
      case '--out':
        options.outPath = takeValue(argv, i, '--out');
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
      case '--json':
        options.json = true;
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

function compileFlowToIr(source) {
  const steps = source
    .split(/\r?\n/)
    .map((line) => line.trim())
    .filter((line) => line.length > 0 && !line.startsWith('#'));
  const primitives = steps.map((line) => {
    const [head, ...rest] = line.split(/\s+/);
    const effect = rest.join(' ').trim();
    const entry = { prim: head };
    if (effect.length > 0) {
      entry.effect = effect;
    }
    return entry;
  });
  return { primitives };
}

async function ensureParentDirectory(path) {
  await mkdir(dirname(path), { recursive: true });
}

async function writeJsonFile(path, value) {
  await ensureParentDirectory(path);
  await writeFile(path, `${JSON.stringify(value, null, 2)}\n`, 'utf8');
}

async function main(argv) {
  let options;
  try {
    options = parseArgs(argv);
  } catch (err) {
    console.error(String(err.message ?? err));
    printUsage();
    process.exitCode = 1;
    return;
  }

  if (options.help) {
    printUsage();
    return;
  }

  if (!options.flowPath && !options.irPath) {
    console.error('Expected --flow <file> or --ir <file>');
    printUsage();
    process.exitCode = 1;
    return;
  }
  if (options.flowPath && options.irPath) {
    console.error('Specify either --flow or --ir, but not both');
    process.exitCode = 1;
    return;
  }

  try {
    let irSource = null;
    if (options.irPath) {
      const irPath = resolve(options.irPath);
      irSource = await readFile(irPath, 'utf8');
    } else if (options.flowPath) {
      const flowPath = resolve(options.flowPath);
      const flowSource = await readFile(flowPath, 'utf8');
      irSource = JSON.stringify(compileFlowToIr(flowSource));
    }

    const result = await run({ irSource, statusPath: options.statusPath ?? undefined, tracePath: options.tracePath ?? undefined });

    if (options.outPath) {
      await writeJsonFile(resolve(options.outPath), result);
    }

    if (options.json) {
      process.stdout.write(`${JSON.stringify(result)}\n`);
    } else {
      const summary = [
        result.status.ok ? 'ok' : 'error',
        `engine=${result.status.engine}`,
        `primitives=${result.status.primitives}`,
        `bytes=${result.status.bytes}`,
      ].join(' ');
      console.log(summary);
    }
  } catch (err) {
    const message = err instanceof Error && typeof err.message === 'string' ? err.message : String(err);
    console.error(`Error: ${message}`);
    process.exitCode = 1;
  }
}

await main(process.argv.slice(2));
