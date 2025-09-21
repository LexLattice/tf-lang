#!/usr/bin/env node
import { mkdir, writeFile } from 'node:fs/promises';
import { join, resolve } from 'node:path';
import process from 'node:process';
import { parseArgs } from 'node:util';

import {
  emitLaw,
  emitFlowEquivalence,
  listLawNames
} from '../packages/tf-l0-proofs/src/smt-laws.mjs';
const LAW_FILE_ALIASES = {
  'commute:emit-metric-with-pure': 'emit_commute.smt2',
  'idempotent:hash': 'idempotent_hash.smt2',
  'idempotent:write-by-key': 'write_idempotent_by_key.smt2',
  'inverse:serialize-deserialize': 'inverse_roundtrip.smt2'
};

const EXTRA_OUTPUTS = [
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

  const outputs = [
    ...listLawNames().map((name) => ({
      file: resolveLawFileName(name),
      generate: () => emitLaw(name)
    })),
    ...EXTRA_OUTPUTS
  ];

  for (const entry of outputs) {
    const outPath = join(targetDir, entry.file);
    const content = entry.generate();
    await writeFile(outPath, ensureTrailingNewline(content), 'utf8');
    process.stdout.write(`wrote ${outPath}\n`);
  }
}

function ensureTrailingNewline(text) {
  return text.endsWith('\n') ? text : `${text}\n`;
}

function resolveLawFileName(name) {
  if (Object.prototype.hasOwnProperty.call(LAW_FILE_ALIASES, name)) {
    return LAW_FILE_ALIASES[name];
  }
  const slug = name
    .toLowerCase()
    .replace(/[^a-z0-9]+/g, '_')
    .replace(/^_+|_+$/g, '');
  return `${slug || 'law'}.smt2`;
}

main(process.argv).catch((error) => {
  process.stderr.write(`${error.message}\n`);
  process.exit(1);
});
