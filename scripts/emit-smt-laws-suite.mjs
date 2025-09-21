#!/usr/bin/env node
import { mkdir, writeFile } from 'node:fs/promises';
import { dirname, join, resolve } from 'node:path';
import process from 'node:process';
import { parseArgs } from 'node:util';

import { emitLaw, emitFlowEquivalence } from '../packages/tf-l0-proofs/src/smt-laws.mjs';

const SUITE = [
  { file: 'idempotent_hash.smt2', kind: 'law', law: 'idempotent:hash' },
  {
    file: 'inverse_roundtrip.smt2',
    kind: 'equiv',
    left: ['serialize', 'deserialize'],
    right: ['id'],
    laws: ['inverse:serialize-deserialize'],
  },
  { file: 'write_idempotent_by_key.smt2', kind: 'law', law: 'idempotent:write-by-key' },
  { file: 'emit_commute.smt2', kind: 'law', law: 'commute:emit-metric-with-pure' },
];

async function main(argv) {
  const { values, positionals } = parseArgs({
    args: argv.slice(2),
    options: {
      out: { type: 'string', short: 'o' },
    },
    allowPositionals: true,
  });

  if (positionals.length > 0) {
    usage('unexpected positional arguments');
    process.exit(2);
  }

  const outDir = typeof values.out === 'string' ? resolve(values.out) : null;
  if (!outDir) {
    usage('missing --out <dir>');
    process.exit(2);
  }

  await mkdir(outDir, { recursive: true });

  for (const entry of SUITE) {
    const target = join(outDir, entry.file);
    const payload = emitEntry(entry);
    await mkdir(dirname(target), { recursive: true });
    await writeFile(target, ensureTrailingNewline(payload), 'utf8');
    process.stdout.write(`wrote ${target}\n`);
  }
}

function emitEntry(entry) {
  if (entry.kind === 'law') {
    return emitLaw(entry.law);
  }
  if (entry.kind === 'equiv') {
    const left = Array.isArray(entry.left) ? entry.left : [];
    const right = Array.isArray(entry.right) ? entry.right : [];
    const laws = Array.isArray(entry.laws) ? entry.laws : [];
    return emitFlowEquivalence(left, right, laws);
  }
  throw new Error(`Unknown suite entry kind: ${entry.kind}`);
}

function ensureTrailingNewline(text) {
  return text.endsWith('\n') ? text : `${text}\n`;
}

function usage(message) {
  if (message) {
    process.stderr.write(`${message}\n`);
  }
  process.stderr.write('Usage: node scripts/emit-smt-laws-suite.mjs -o <outDir>\n');
}

main(process.argv).catch((error) => {
  process.stderr.write(`${error?.stack || error}\n`);
  process.exit(1);
});
