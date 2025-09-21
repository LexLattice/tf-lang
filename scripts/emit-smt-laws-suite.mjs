#!/usr/bin/env node
import { mkdir, writeFile } from 'node:fs/promises';
import { dirname, join, resolve } from 'node:path';
import process from 'node:process';
import { parseArgs } from 'node:util';

import {
  emitLaw,
  listLawNames
} from '../packages/tf-l0-proofs/src/smt-laws.mjs';

const LAW_FILENAME_OVERRIDES = new Map([
  ['commute:emit-metric-with-pure', 'emit_commute.smt2'],
  ['idempotent:hash', 'idempotent_hash.smt2'],
  ['idempotent:write-by-key', 'write_idempotent_by_key.smt2'],
  ['inverse:serialize-deserialize', 'inverse_roundtrip.smt2']
]);

async function main(argv) {
  const { values } = parseArgs({
    args: argv.slice(2),
    options: {
      out: { type: 'string', short: 'o' }
    },
    allowPositionals: false
  });

  const outDir = typeof values.out === 'string' ? resolve(values.out) : null;
  if (!outDir) {
    usage('missing --out <dir>');
    process.exit(2);
  }

  await mkdir(outDir, { recursive: true });

  const lawNames = listLawNames();
  const written = [];

  for (const lawName of lawNames) {
    const fileName = LAW_FILENAME_OVERRIDES.get(lawName) ?? `${sanitize(lawName)}.smt2`;
    const filePath = join(outDir, fileName);
    const content = ensureTrailingNewline(emitLaw(lawName));
    await mkdir(dirname(filePath), { recursive: true });
    await writeFile(filePath, content, 'utf8');
    written.push(filePath);
  }

  written.sort((a, b) => a.localeCompare(b));
  for (const filePath of written) {
    process.stdout.write(`wrote ${filePath}\n`);
  }
}

function sanitize(name) {
  return name
    .toLowerCase()
    .replace(/[^a-z0-9]+/gi, '_')
    .replace(/_+/g, '_')
    .replace(/^_+|_+$/g, '');
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
  process.stderr.write('Usage: node scripts/emit-smt-laws-suite.mjs -o <out-dir>\n');
}

main(process.argv).catch((error) => {
  process.stderr.write(`${error?.message ?? error}\n`);
  process.exit(1);
});
