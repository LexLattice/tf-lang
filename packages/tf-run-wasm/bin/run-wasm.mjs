#!/usr/bin/env node
import { readFile, writeFile, mkdir } from 'node:fs/promises';
import { dirname, resolve } from 'node:path';
import process from 'node:process';

import { run } from '../dist/index.js';

function printUsage() {
  console.log(`Usage: tf-run-wasm (--ir <file.ir.json> | --flow <file.tf>) [--out <file>] [--status <file>] [--trace <file>] [--json]`);
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
    if (arg === '--help' || arg === '-h') {
      options.help = true;
      break;
    } else if (arg === '--flow') {
      i += 1;
      options.flowPath = argv[i] ?? null;
    } else if (arg === '--ir') {
      i += 1;
      options.irPath = argv[i] ?? null;
    } else if (arg === '--out') {
      i += 1;
      options.outPath = argv[i] ?? null;
    } else if (arg === '--status') {
      i += 1;
      options.statusPath = argv[i] ?? null;
    } else if (arg === '--trace') {
      i += 1;
      options.tracePath = argv[i] ?? null;
    } else if (arg === '--json') {
      options.json = true;
    } else {
      throw new Error(`Unknown argument: ${arg}`);
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

    const result = await run({ irSource, statusPath: options.statusPath, tracePath: options.tracePath });

    if (options.outPath) {
      await writeJsonFile(resolve(options.outPath), result);
    }

    if (options.json) {
      process.stdout.write(`${JSON.stringify(result)}\n`);
    }
  } catch (err) {
    const message = err instanceof Error && typeof err.message === 'string' ? err.message : String(err);
    console.error(`Error: ${message}`);
    process.exitCode = 1;
  }
}

await main(process.argv.slice(2));
