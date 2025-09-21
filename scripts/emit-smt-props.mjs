#!/usr/bin/env node
import { readFile, writeFile, mkdir } from 'node:fs/promises';
import { dirname, resolve } from 'node:path';
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
    options: {
      out: { type: 'string', short: 'o' },
    },
    allowPositionals: true,
  });

  const outPath = typeof values.out === 'string' ? resolve(values.out) : null;
  if (!outPath) {
    usage('missing --out <file>');
    process.exit(2);
  }

  const [mode, ...rest] = positionals;
  if (!mode) {
    usage('missing mode');
    process.exit(2);
  }

  if (mode === 'par-safety') {
    if (rest.length !== 1) {
      usage('par-safety requires exactly one input');
      process.exit(2);
    }
    const ir = await loadIR(rest[0]);
    const smt = emitParWriteSafety(ir);
    await writeOutput(outPath, smt);
    process.stdout.write(`wrote ${outPath}\n`);
    return;
  }

  if (mode === 'commute') {
    if (rest.length !== 2) {
      usage('commute requires two inputs');
      process.exit(2);
    }
    const [left, right] = await Promise.all(rest.map((entry) => loadIR(entry)));
    const smt = emitCommutationEquiv(left, right);
    await writeOutput(outPath, smt);
    process.stdout.write(`wrote ${outPath}\n`);
    return;
  }

  usage(`unknown mode: ${mode}`);
  process.exit(2);
}

function usage(message) {
  if (message) {
    process.stderr.write(`${message}\n`);
  }
  process.stderr.write(
    'Usage:\n' +
      '  node scripts/emit-smt-props.mjs par-safety <input.tf|input.ir.json> -o <out.smt2>\n' +
      '  node scripts/emit-smt-props.mjs commute <seqEP.tf|.ir.json> <seqPE.tf|.ir.json> -o <out.smt2>\n'
  );
}

async function loadIR(source) {
  const resolved = resolve(source);
  const contents = await readFile(resolved, 'utf8');
  if (resolved.endsWith('.tf')) {
    return parseDSL(contents);
  }
  if (resolved.endsWith('.ir.json')) {
    return JSON.parse(contents);
  }
  throw new Error('unsupported input; expected .tf or .ir.json');
}

async function writeOutput(filePath, content) {
  await mkdir(dirname(filePath), { recursive: true });
  await writeFile(filePath, ensureTrailingNewline(content), 'utf8');
}

function ensureTrailingNewline(text) {
  return text.endsWith('\n') ? text : `${text}\n`;
}

main(process.argv).catch((error) => {
  process.stderr.write(`${error.message}\n`);
  process.exit(1);
});
