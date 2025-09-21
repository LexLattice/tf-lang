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
    usage();
    process.exit(1);
  }

  const mode = positionals[0];
  const outPath = typeof values.out === 'string' ? resolve(values.out) : null;
  if (!outPath) {
    usage('missing --out <file>');
    process.exit(2);
  }

  let smt;
  if (mode === 'par-safety') {
    if (positionals.length !== 2) {
      usage('par-safety requires exactly one input flow');
      process.exit(1);
    }
    const ir = await loadIR(positionals[1]);
    smt = emitParWriteSafety(ir);
  } else if (mode === 'commute') {
    if (positionals.length !== 3) {
      usage('commute requires exactly two input flows');
      process.exit(1);
    }
    const [leftPath, rightPath] = positionals.slice(1);
    const [leftIR, rightIR] = await Promise.all([loadIR(leftPath), loadIR(rightPath)]);
    smt = emitCommutationEquiv(leftIR, rightIR);
  } else {
    usage(`unknown mode: ${mode}`);
    process.exit(1);
  }

  await mkdir(dirname(outPath), { recursive: true });
  await writeFile(outPath, ensureTrailingNewline(smt), 'utf8');
  process.stdout.write(`wrote ${outPath}\n`);
}

async function loadIR(sourcePath) {
  const resolved = resolve(sourcePath);
  const lower = sourcePath.toLowerCase();
  const raw = await readFile(resolved, 'utf8');
  if (lower.endsWith('.tf')) {
    return parseDSL(raw);
  }
  if (lower.endsWith('.ir.json')) {
    return JSON.parse(raw);
  }
  throw new Error('unsupported input; expected .tf or .ir.json');
}

function usage(message) {
  if (message) {
    process.stderr.write(`${message}\n`);
  }
  process.stderr.write(
    'Usage:\n' +
      '  node scripts/emit-smt-props.mjs par-safety <flow.tf|flow.ir.json> -o <out.smt2>\n' +
      '  node scripts/emit-smt-props.mjs commute <flowA> <flowB> -o <out.smt2>\n'
  );
}

function ensureTrailingNewline(text) {
  if (text.endsWith('\n')) {
    return text;
  }
  return `${text}\n`;
}

main(process.argv).catch((error) => {
  process.stderr.write(`${error.message}\n`);
  process.exit(1);
});
