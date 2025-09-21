#!/usr/bin/env node
import { readFile, writeFile, mkdir } from 'node:fs/promises';
import path from 'node:path';
import process from 'node:process';

import { emitAlloy } from '../packages/tf-l0-proofs/src/alloy.mjs';
import { parseDSL } from '../packages/tf-compose/src/parser.mjs';

async function main() {
  const [input, ...rest] = process.argv.slice(2);
  if (!input) {
    usage('missing input file');
  }

  let output = null;
  for (let i = 0; i < rest.length; i++) {
    const arg = rest[i];
    if (arg === '-o') {
      output = rest[++i];
    }
  }

  if (!output) {
    usage('missing -o <output> option');
  }

  const resolvedInput = path.resolve(process.cwd(), input);
  const resolvedOutput = path.resolve(process.cwd(), output);

  const ir = await loadIR(resolvedInput);
  const alloy = emitAlloy(ir);

  await mkdir(path.dirname(resolvedOutput), { recursive: true });
  await writeFile(resolvedOutput, alloy, 'utf8');
  process.stdout.write(`wrote ${resolvedOutput}\n`);
}

async function loadIR(inputPath) {
  if (inputPath.endsWith('.ir.json')) {
    const raw = await readFile(inputPath, 'utf8');
    return JSON.parse(raw);
  }
  if (inputPath.endsWith('.tf')) {
    const source = await readFile(inputPath, 'utf8');
    return parseDSL(source);
  }
  throw new Error(`unsupported input format for ${inputPath}`);
}

function usage(message) {
  const text = message ? `${message}\n` : '';
  process.stderr.write(
    `${text}usage: node scripts/emit-alloy.mjs <input.ir.json|input.tf> -o <output.als>\n`
  );
  process.exit(1);
}

await main().catch((err) => {
  process.stderr.write(`${err.message}\n`);
  process.exit(1);
});
