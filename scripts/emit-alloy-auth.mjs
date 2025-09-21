#!/usr/bin/env node
import { readFile, writeFile, mkdir } from 'node:fs/promises';
import { dirname, resolve } from 'node:path';
import process from 'node:process';
import { parseArgs } from 'node:util';

import { parseDSL } from '../packages/tf-compose/src/parser.mjs';
import { emitAuthorizeAlloy } from '../packages/tf-l0-proofs/src/alloy-auth.mjs';

async function main(argv) {
  const { values, positionals } = parseArgs({
    args: argv.slice(2),
    options: {
      out: { type: 'string', short: 'o' }
    },
    allowPositionals: true
  });

  if (positionals.length !== 1 || typeof values.out !== 'string') {
    usage();
    process.exit(2);
  }

  const inputPath = resolve(positionals[0]);
  const outPath = resolve(values.out);

  const ir = await loadIR(inputPath);
  const alloy = ensureTrailingNewline(emitAuthorizeAlloy(ir));

  await mkdir(dirname(outPath), { recursive: true });
  await writeFile(outPath, alloy, 'utf8');
  process.stdout.write(`wrote ${outPath}\n`);
}

async function loadIR(sourcePath) {
  if (sourcePath.endsWith('.tf')) {
    const raw = await readFile(sourcePath, 'utf8');
    return parseDSL(raw);
  }
  if (sourcePath.endsWith('.ir.json')) {
    const raw = await readFile(sourcePath, 'utf8');
    return JSON.parse(raw);
  }
  throw new Error('unsupported input; expected .tf or .ir.json');
}

function ensureTrailingNewline(text) {
  if (text.endsWith('\n')) {
    return text;
  }
  return `${text}\n`;
}

function usage() {
  process.stderr.write('Usage: node scripts/emit-alloy-auth.mjs <flow.tf|flow.ir.json> -o <out.als>\n');
}

main(process.argv).catch((error) => {
  process.stderr.write(`${error?.message ?? error}\n`);
  process.exit(1);
});
