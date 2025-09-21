#!/usr/bin/env node
import { readFile, writeFile, mkdir } from 'node:fs/promises';
import { dirname, resolve } from 'node:path';
import process from 'node:process';
import { parseArgs } from 'node:util';

import { parseDSL } from '../packages/tf-compose/src/parser.mjs';
import { emitAlloyAuthorize } from '../packages/tf-l0-proofs/src/alloy-auth.mjs';

async function main(argv) {
  const { values, positionals } = parseArgs({
    args: argv.slice(2),
    options: {
      out: { type: 'string', short: 'o' },
      rules: { type: 'string' },
    },
    allowPositionals: true,
  });

  if (positionals.length !== 1 || typeof values.out !== 'string') {
    usage();
    process.exit(2);
  }

  const inputPath = resolve(positionals[0]);
  const outPath = resolve(values.out);
  const rulesPath = resolveRulesPath(values.rules);

  const [ir, rules] = await Promise.all([loadIR(inputPath), loadRules(rulesPath)]);
  const alloy = emitAlloyAuthorize(ir, { rules });

  await mkdir(dirname(outPath), { recursive: true });
  await writeFile(outPath, alloy, 'utf8');
  process.stdout.write(`wrote ${outPath}\n`);
}

function usage() {
  process.stderr.write('Usage: node scripts/emit-alloy-auth.mjs <input.tf|input.ir.json> -o <out.als> [--rules path]\n');
}

function resolveRulesPath(raw) {
  if (typeof raw === 'string' && raw.length > 0) {
    return resolve(raw);
  }
  return new URL('../packages/tf-l0-check/rules/authorize-scopes.json', import.meta.url);
}

async function loadIR(srcPath) {
  if (srcPath.endsWith('.tf')) {
    const source = await readFile(srcPath, 'utf8');
    return parseDSL(source);
  }
  if (srcPath.endsWith('.ir.json')) {
    const raw = await readFile(srcPath, 'utf8');
    return JSON.parse(raw);
  }
  throw new Error('unsupported input; expected .tf or .ir.json');
}

async function loadRules(source) {
  if (source instanceof URL) {
    const raw = await readFile(source, 'utf8');
    return JSON.parse(raw);
  }
  const raw = await readFile(source, 'utf8');
  return JSON.parse(raw);
}

main(process.argv).catch((error) => {
  process.stderr.write(`${error.message}\n`);
  process.exit(1);
});

