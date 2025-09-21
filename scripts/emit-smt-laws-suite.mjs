#!/usr/bin/env node
import { mkdir, writeFile } from 'node:fs/promises';
import { join, resolve } from 'node:path';
import process from 'node:process';
import { parseArgs } from 'node:util';

import { emitLaw, emitFlowEquivalence } from '../packages/tf-l0-proofs/src/smt-laws.mjs';

const OUTPUTS = [
  {
    file: 'idempotent_hash.smt2',
    generate: () => emitLaw('idempotent:hash')
  },
  {
    file: 'inverse_roundtrip.smt2',
    generate: () => emitLaw('inverse:serialize-deserialize')
  },
  {
    file: 'emit_commute.smt2',
    generate: () => emitLaw('commute:emit-metric-with-pure')
  },
  {
    file: 'write_idempotent_by_key.smt2',
    generate: () => emitLaw('idempotent:write-by-key')
  },
  {
    file: 'serialize_deserialize_equiv.smt2',
    generate: () =>
      emitFlowEquivalence(
        ['serialize', 'deserialize'],
        [],
        ['inverse:serialize-deserialize']
      )
  }
];

async function main(argv) {
  const { values } = parseArgs({
    args: argv.slice(2),
    options: {
      out: { type: 'string', short: 'o' }
    }
  });

  if (typeof values.out !== 'string' || values.out.trim().length === 0) {
    process.stderr.write('Usage: node scripts/emit-smt-laws-suite.mjs -o <outDir>\n');
    process.exit(2);
  }

  const targetDir = resolve(values.out);
  await mkdir(targetDir, { recursive: true });

  for (const entry of OUTPUTS) {
    const outPath = join(targetDir, entry.file);
    const content = entry.generate();
    await writeFile(outPath, ensureTrailingNewline(content), 'utf8');
    process.stdout.write(`wrote ${outPath}\n`);
  }
}

function ensureTrailingNewline(text) {
  return text.endsWith('\n') ? text : `${text}\n`;
}

main(process.argv).catch((error) => {
  process.stderr.write(`${error.message}\n`);
  process.exit(1);
});
