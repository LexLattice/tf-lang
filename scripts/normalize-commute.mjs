#!/usr/bin/env node
import { readFile, writeFile, mkdir } from 'node:fs/promises';
import path from 'node:path';
import { pathToFileURL } from 'node:url';
import { parseArgs } from 'node:util';
import process from 'node:process';

import { normalize } from '../packages/tf-l0-ir/src/normalize.mjs';
import { canonicalize } from '../packages/tf-l0-ir/src/hash.mjs';

async function main(argv) {
  const cliArgs = argv.slice(2);
  const { values, positionals } = parseArgs({
    args: cliArgs,
    options: {
      o: { type: 'string' }
    },
    allowPositionals: true
  });

  if (positionals.length !== 1) {
    throw new Error('Usage: node scripts/normalize-commute.mjs <flow.tf|flow.ir.json> -o <output.ir.json>');
  }

  const outputPath = values.o;
  if (typeof outputPath !== 'string' || outputPath.length === 0) {
    throw new Error('Usage: node scripts/normalize-commute.mjs <flow.tf|flow.ir.json> -o <output.ir.json>');
  }

  const inputPath = path.resolve(process.cwd(), positionals[0]);
  const resolvedOutput = path.resolve(process.cwd(), outputPath);

  const ir = await loadIR(inputPath);
  const normalized = normalize(ir);

  await mkdir(path.dirname(resolvedOutput), { recursive: true });
  await writeFile(resolvedOutput, `${canonicalize(normalized)}\n`, 'utf8');
}

async function loadIR(filePath) {
  if (filePath.endsWith('.tf')) {
    const source = await readFile(filePath, 'utf8');
    const { parseDSL } = await import('../packages/tf-compose/src/parser.mjs');
    return parseDSL(source);
  }

  if (filePath.endsWith('.ir.json')) {
    const contents = await readFile(filePath, 'utf8');
    return JSON.parse(contents);
  }

  throw new Error('Input must end with .tf or .ir.json');
}

if (process.argv[1] && import.meta.url === pathToFileURL(path.resolve(process.argv[1])).href) {
  main(process.argv).catch((err) => {
    const message = err && typeof err.message === 'string' ? err.message : String(err);
    console.error(message);
    process.exitCode = 1;
  });
}
