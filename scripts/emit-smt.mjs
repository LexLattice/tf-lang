#!/usr/bin/env node
import { readFile, writeFile, mkdir } from 'node:fs/promises';
import { dirname } from 'node:path';

import { parseDSL } from '../packages/tf-compose/src/parser.mjs';
import { emitSMT } from '../packages/tf-l0-proofs/src/smt.mjs';

const args = process.argv.slice(2);
if (args.length === 0) {
  console.error('Usage: node scripts/emit-smt.mjs <flow.tf> -o <out.smt2>');
  process.exit(2);
}

const flowPath = args[0];
if (!flowPath) {
  console.error('Missing flow path.');
  process.exit(2);
}

let outPath = null;
for (let i = 1; i < args.length; i++) {
  if (args[i] === '-o' || args[i] === '--out') {
    outPath = args[i + 1] || null;
    break;
  }
}

if (!outPath) {
  console.error('Missing output path.');
  process.exit(2);
}

const source = await readFile(flowPath, 'utf8');
const ir = parseDSL(source);
const payload = emitSMT(ir);

await mkdir(dirname(outPath), { recursive: true });
await writeFile(outPath, payload, 'utf8');
