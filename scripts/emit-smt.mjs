#!/usr/bin/env node
import { readFile, writeFile, mkdir } from 'node:fs/promises';
import { dirname, resolve } from 'node:path';
import process from 'node:process';

import { parseDSL } from '../packages/tf-compose/src/parser.mjs';
import { emitSMT } from '../packages/tf-l0-proofs/src/smt.mjs';

async function main(argv) {
  const args = argv.slice(2);
  if (args.length === 0) {
    usage();
    process.exit(1);
  }

  const input = args[0];
  let output = null;

  for (let i = 1; i < args.length; i++) {
    const part = args[i];
    if (part === '-o' || part === '--output') {
      output = args[i + 1] || null;
      i++;
    }
  }

  if (!output) {
    usage();
    process.exit(1);
  }

  const srcPath = resolve(input);
  const outPath = resolve(output);
  const raw = await readFile(srcPath, 'utf8');
  const ir = parseDSL(raw);
  const smt = emitSMT(ir);

  await mkdir(dirname(outPath), { recursive: true });
  await writeFile(outPath, smt, 'utf8');
  process.stdout.write(`wrote ${outPath}\n`);
}

function usage() {
  process.stderr.write('Usage: node scripts/emit-smt.mjs <flow.tf> -o <output.smt2>\n');
}

main(process.argv).catch((err) => {
  process.stderr.write(String(err?.stack || err));
  process.stderr.write('\n');
  process.exit(1);
});
