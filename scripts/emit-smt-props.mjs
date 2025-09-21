#!/usr/bin/env node
import { readFile, writeFile, mkdir } from 'node:fs/promises';
import { basename, dirname, extname, resolve } from 'node:path';
import process from 'node:process';
import { parseArgs } from 'node:util';

import { parseDSL } from '../packages/tf-compose/src/parser.mjs';
import {
  emitParWriteSafety,
  emitCommutationEquiv,
} from '../packages/tf-l0-proofs/src/smt-props.mjs';

async function main(argv) {
  const { values, positionals } = parseArgs({
    args: argv.slice(2),
    options: { out: { type: 'string', short: 'o' } },
    allowPositionals: true,
  });

  if (positionals.length < 2) {
    usage();
    process.exit(1);
  }

  const mode = positionals[0];
  const inputs = positionals.slice(1);
  const catalog = await loadCatalog();
  let smt = '';

  if (mode === 'par-safety') {
    if (inputs.length !== 1) {
      usage();
      process.exit(1);
    }
    const ir = await loadIR(inputs[0]);
    smt = emitParWriteSafety(ir, { catalog });
  } else if (mode === 'commute') {
    if (inputs.length !== 2) {
      usage();
      process.exit(1);
    }
    const irA = await loadIR(inputs[0]);
    const irB = await loadIR(inputs[1]);
    smt = emitCommutationEquiv(irA, irB, { catalog });
  } else {
    usage();
    process.exit(1);
  }

  const outPath = resolve(values.out ?? defaultOut(mode, inputs));
  await mkdir(dirname(outPath), { recursive: true });
  await writeFile(outPath, smt, 'utf8');
  process.stdout.write(`wrote ${outPath}\n`);
}

function usage() {
  process.stderr.write(
    'Usage:\n' +
      '  node scripts/emit-smt-props.mjs par-safety <flow.tf|flow.ir.json> [-o out/0.4/proofs/props/<name>.smt2]\n' +
      '  node scripts/emit-smt-props.mjs commute <flowA.tf|flowA.ir.json> <flowB.tf|flowB.ir.json> [-o out/0.4/proofs/props/<name>.smt2]\n'
  );
}

function defaultOut(mode, inputs) {
  const first = inputs[0] ?? mode;
  const base = basename(first);
  const ext = extname(base);
  const stem = ext ? base.slice(0, -ext.length) : base;
  const suffix = mode === 'par-safety' ? 'par-safety' : 'commute';
  return `out/0.4/proofs/props/${stem}.${suffix}.smt2`;
}

async function loadIR(inputPath) {
  const resolved = resolve(inputPath);
  if (resolved.endsWith('.tf')) {
    const raw = await readFile(resolved, 'utf8');
    return parseDSL(raw);
  }
  if (resolved.endsWith('.ir.json')) {
    const raw = await readFile(resolved, 'utf8');
    return JSON.parse(raw);
  }
  throw new Error(`Unsupported input format: ${inputPath}`);
}

async function loadCatalog() {
  const catalogUrl = new URL('../packages/tf-l0-spec/spec/catalog.json', import.meta.url);
  const raw = await readFile(catalogUrl, 'utf8');
  return JSON.parse(raw);
}

main(process.argv).catch((err) => {
  process.stderr.write(String(err?.stack || err));
  process.stderr.write('\n');
  process.exit(1);
});
