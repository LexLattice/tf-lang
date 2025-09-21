#!/usr/bin/env node
import { readFile, writeFile, mkdir } from 'node:fs/promises';
import path from 'node:path';
import { pathToFileURL } from 'node:url';

import { normalize } from '../packages/tf-l0-ir/src/normalize.mjs';
import { parseDSL } from '../packages/tf-compose/src/parser.mjs';

function usage() {
  console.error('Usage: node scripts/normalize-commute.mjs <flow.tf|flow.ir.json> [-o <output.ir.json>]');
}

async function loadInput(p) {
  const source = await readFile(p, 'utf8');
  const ext = path.extname(p).toLowerCase();
  if (ext === '.tf') {
    return parseDSL(source);
  }
  if (ext === '.json') {
    return JSON.parse(source);
  }
  throw new Error('Unsupported input format. Expected .tf or .ir.json');
}

async function main() {
  const args = process.argv.slice(2);
  if (args.length === 0) {
    usage();
    process.exit(2);
  }

  const inputPath = args[0];
  if (!inputPath) {
    usage();
    process.exit(2);
  }

  let outputPath = null;
  for (let i = 1; i < args.length; i++) {
    const arg = args[i];
    if (arg === '-o') {
      outputPath = args[i + 1] || null;
      i += 1;
    }
  }

  if (!outputPath && args.includes('-o')) {
    const index = args.indexOf('-o');
    if (index === args.length - 1) {
      console.error('Missing value for -o');
      process.exit(2);
    }
  }

  let ir;
  try {
    ir = await loadInput(inputPath);
  } catch (err) {
    console.error(`Failed to read ${inputPath}:`, err.message);
    process.exit(1);
  }

  const normalized = normalize(ir);
  const serialized = JSON.stringify(normalized, null, 2) + '\n';

  if (outputPath) {
    await mkdir(path.dirname(outputPath), { recursive: true });
    await writeFile(outputPath, serialized, 'utf8');
  } else {
    process.stdout.write(serialized);
  }
}

if (import.meta.url === pathToFileURL(process.argv[1] ?? '').href) {
  await main();
}
