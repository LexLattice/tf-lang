#!/usr/bin/env node
import { readFile, writeFile, mkdir } from 'node:fs/promises';
import { dirname, resolve } from 'node:path';
import process from 'node:process';
import { parseArgs } from 'node:util';

import { parseDSL } from '../packages/tf-compose/src/parser.mjs';
import { emitParWriteSafety, emitCommutationEquiv } from '../packages/tf-l0-proofs/src/smt-props.mjs';

async function main(argv) {
  const { values, positionals } = parseArgs({
    args: argv.slice(2),
    options: {
      out: { type: 'string', short: 'o' },
    },
    allowPositionals: true,
  });

  if (positionals.length === 0) {
    usage('missing command');
    process.exit(2);
  }

  const command = positionals[0];
  const inputs = positionals.slice(1);
  const outPath = typeof values.out === 'string' ? resolve(values.out) : null;

  if (!outPath) {
    usage('missing --out <file>');
    process.exit(2);
  }

  const catalog = await loadCatalog();

  if (command === 'par-safety') {
    if (inputs.length !== 1) {
      usage('par-safety requires exactly one input');
      process.exit(2);
    }
    const ir = await loadIR(inputs[0]);
    const smt = emitParWriteSafety(ir, { catalog });
    await writeOutput(outPath, smt);
    process.stdout.write(`wrote ${outPath}\n`);
    return;
  }

  if (command === 'commute') {
    if (inputs.length !== 2) {
      usage('commute requires two inputs');
      process.exit(2);
    }
    const [left, right] = await Promise.all(inputs.map((entry) => loadIR(entry)));
    const smt = emitCommutationEquiv(left, right, { catalog });
    await writeOutput(outPath, smt);
    process.stdout.write(`wrote ${outPath}\n`);
    return;
  }

  usage(`unknown command: ${command}`);
  process.exit(2);
}

async function loadIR(source) {
  const resolved = resolve(source);
  if (resolved.endsWith('.tf')) {
    const raw = await readFile(resolved, 'utf8');
    return parseDSL(raw);
  }
  if (resolved.endsWith('.ir.json')) {
    const raw = await readFile(resolved, 'utf8');
    return JSON.parse(raw);
  }
  throw new Error('unsupported input; expected .tf or .ir.json');
}

async function loadCatalog() {
  try {
    const raw = await readFile('packages/tf-l0-spec/spec/catalog.json', 'utf8');
    return JSON.parse(raw);
  } catch {
    return { primitives: [] };
  }
}

async function writeOutput(filePath, content) {
  await mkdir(dirname(filePath), { recursive: true });
  await writeFile(filePath, ensureTrailingNewline(content), 'utf8');
}

function ensureTrailingNewline(text) {
  if (text.endsWith('\n')) {
    return text;
  }
  return `${text}\n`;
}

function usage(message) {
  if (message) {
    process.stderr.write(`${message}\n`);
  }
  process.stderr.write(
    'Usage:\n' +
      '  node scripts/emit-smt-props.mjs par-safety <flow.tf|flow.ir.json> -o <out.smt2>\n' +
      '  node scripts/emit-smt-props.mjs commute <seqEP> <seqPE> -o <out.smt2>\n'
  );
}

main(process.argv).catch((error) => {
  process.stderr.write(`${error.message}\n`);
  process.exit(1);
});
