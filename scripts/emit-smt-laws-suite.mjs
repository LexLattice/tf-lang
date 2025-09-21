#!/usr/bin/env node
import { mkdir, writeFile } from 'node:fs/promises';
import { join, resolve } from 'node:path';
import process from 'node:process';
import { parseArgs } from 'node:util';

import { emitLaw, emitFlowEquivalence } from '../packages/tf-l0-proofs/src/smt-laws.mjs';

const SUITE = [
  {
    file: 'commute_emit_metric_with_pure.smt2',
    build: () => emitLaw('commute:emit-metric-with-pure'),
  },
  {
    file: 'idempotent_hash.smt2',
    build: () => emitLaw('idempotent:hash'),
  },
  {
    file: 'inverse_roundtrip.smt2',
    build: () =>
      emitFlowEquivalence(['serialize', 'deserialize'], [], ['inverse:serialize-deserialize']),
  },
  {
    file: 'write_idempotent_by_key.smt2',
    build: () => emitLaw('idempotent:write-by-key'),
  },
];

async function main(argv) {
  const { values } = parseArgs({
    args: argv.slice(2),
    options: {
      out: { type: 'string', short: 'o' },
    },
  });

  if (typeof values.out !== 'string' || values.out.length === 0) {
    usage();
    process.exit(2);
  }

  const outDir = resolve(values.out);
  await mkdir(outDir, { recursive: true });

  for (const entry of SUITE) {
    const target = join(outDir, entry.file);
    const smt = ensureTrailingNewline(entry.build());
    await writeFile(target, smt, 'utf8');
    process.stdout.write(`wrote ${target}\n`);
  }
}

function usage() {
  process.stderr.write('Usage: node scripts/emit-smt-laws-suite.mjs -o <outDir>\n');
}

function ensureTrailingNewline(text) {
  return text.endsWith('\n') ? text : `${text}\n`;
}

main(process.argv).catch((error) => {
  process.stderr.write(`${error.message}\n`);
  process.exit(1);
});

