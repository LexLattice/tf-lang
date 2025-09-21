#!/usr/bin/env node
import { readFile, writeFile, mkdir } from 'node:fs/promises';
import path from 'node:path';

const normalizeMod = await import('../packages/tf-l0-ir/src/normalize.mjs');

async function loadParser() {
  try {
    return await import('../packages/tf-compose/src/parser.mjs');
  } catch {
    return import('../packages/tf-compose/src/parser.with-regions.mjs');
  }
}

async function loadIR(filePath) {
  if (filePath.endsWith('.tf')) {
    const parser = await loadParser();
    const source = await readFile(filePath, 'utf8');
    return parser.parseDSL(source);
  }

  const text = await readFile(filePath, 'utf8');
  return JSON.parse(text);
}

function printUsage() {
  console.error('Usage: node scripts/normalize-commute.mjs <flow.tf|flow.ir.json> [-o output.ir.json]');
}

const args = process.argv.slice(2);
if (args.length === 0) {
  printUsage();
  process.exit(2);
}

const inputPath = args[0];
let outputPath = null;
for (let i = 1; i < args.length; i++) {
  const arg = args[i];
  if (arg === '-o' || arg === '--output') {
    if (i + 1 >= args.length) {
      console.error('normalize-commute: missing value for', arg);
      process.exit(2);
    }
    outputPath = args[i + 1];
    i++;
  }
}

const ir = await loadIR(inputPath);
const normalized = normalizeMod.normalize(ir);
const serialized = JSON.stringify(normalized, null, 2) + '\n';

if (outputPath) {
  await mkdir(path.dirname(outputPath), { recursive: true });
  await writeFile(outputPath, serialized, 'utf8');
} else {
  process.stdout.write(serialized);
}
