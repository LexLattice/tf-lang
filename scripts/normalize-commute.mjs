#!/usr/bin/env node
import { readFile, writeFile, mkdir } from 'node:fs/promises';
import path from 'node:path';

import { normalize } from '../packages/tf-l0-ir/src/normalize.mjs';
import { parseDSL } from '../packages/tf-compose/src/parser.mjs';

function usage() {
  console.error('Usage: node scripts/normalize-commute.mjs <flow.tf|flow.ir.json> -o <output.ir.json>');
  process.exit(2);
}

function parseArgs(argv) {
  let input = null;
  let output = null;
  for (let i = 0; i < argv.length; i++) {
    const arg = argv[i];
    if (arg === '-o') {
      const next = argv[++i];
      if (!next) {
        usage();
      }
      output = next;
    } else if (!input) {
      input = arg;
    } else {
      usage();
    }
  }
  if (!input || !output) {
    usage();
  }
  return { input, output };
}

async function loadIR(filePath) {
  const raw = await readFile(filePath, 'utf8');
  if (filePath.endsWith('.ir.json')) {
    return JSON.parse(raw);
  }
  if (filePath.endsWith('.tf')) {
    return parseDSL(raw);
  }
  console.error('Input must be a .tf or .ir.json file');
  process.exit(2);
}

async function main() {
  const { input, output } = parseArgs(process.argv.slice(2));
  const ir = await loadIR(input);
  const normalized = normalize(ir);
  const serialized = JSON.stringify(normalized, null, 2) + '\n';
  await mkdir(path.dirname(output), { recursive: true });
  await writeFile(output, serialized, 'utf8');
}

await main();
