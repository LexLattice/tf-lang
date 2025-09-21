#!/usr/bin/env node
import { readFile, writeFile, mkdir } from 'node:fs/promises';
import { basename, dirname, extname, resolve } from 'node:path';
import process from 'node:process';
import { parseArgs } from 'node:util';

import { parseDSL } from '../packages/tf-compose/src/parser.mjs';
import { emitAlloy } from '../packages/tf-l0-proofs/src/alloy.mjs';

async function main(argv) {
  const { values, positionals } = parseArgs({
    args: argv.slice(2),
    options: { out: { type: 'string', short: 'o' } },
    allowPositionals: true
  });

  if (positionals.length !== 1) {
    usage();
    process.exit(1);
  }

  const inputPath = positionals[0];
  const outputArg = values.out ?? defaultOut(inputPath);
  const srcPath = resolve(inputPath);
  const outPath = resolve(outputArg);

  const ir = await loadIR(srcPath);
  const alloy = emitAlloy(ir);

  await mkdir(dirname(outPath), { recursive: true });
  await writeFile(outPath, alloy, 'utf8');
  process.stdout.write(`wrote ${outPath}\n`);
}

function usage() {
  process.stderr.write(
    'Usage: node scripts/emit-alloy.mjs <input.ir.json|input.tf> [-o out/0.4/proofs/<name>.als>]\n'
  );
}

function defaultOut(inputPath) {
  const base = basename(inputPath);
  if (base.endsWith('.ir.json')) {
    const stem = base.slice(0, -'.ir.json'.length);
    return `out/0.4/proofs/${stem}.als`;
  }
  const ext = extname(base);
  const stem = ext ? base.slice(0, -ext.length) : base;
  return `out/0.4/proofs/${stem}.als`;
}

async function loadIR(srcPath) {
  if (srcPath.endsWith('.ir.json')) {
    const raw = await readFile(srcPath, 'utf8');
    return JSON.parse(raw);
  }
  if (srcPath.endsWith('.tf')) {
    const raw = await readFile(srcPath, 'utf8');
    return parseDSL(raw);
  }
  throw new Error('Unsupported input type; expected .ir.json or .tf');
}

main(process.argv).catch((err) => {
  process.stderr.write(String(err?.stack || err));
  process.stderr.write('\n');
  process.exit(1);
});
