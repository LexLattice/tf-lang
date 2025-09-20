#!/usr/bin/env node
import { readFile, writeFile, mkdir } from 'node:fs/promises';
import { dirname } from 'node:path';

import { parseDSL } from '../src/parser.mjs';
import { checkIR } from '../../tf-l0-check/src/check.mjs';
import { manifestFromVerdict } from '../../tf-l0-check/src/manifest.mjs';

async function loadCatalog() {
  try {
    const raw = await readFile('packages/tf-l0-spec/spec/catalog.json', 'utf8');
    return JSON.parse(raw);
  } catch {
    return { primitives: [] };
  }
}

function printUsage() {
  console.error('Usage: node packages/tf-compose/bin/tf-manifest.mjs <flow.tf> [-o out.json]');
}

const args = process.argv.slice(2);
let inputPath = null;
let outputPath = null;
for (let i = 0; i < args.length; i += 1) {
  const arg = args[i];
  if (arg === '-o' || arg === '--out') {
    if (i + 1 >= args.length) {
      printUsage();
      process.exit(2);
    }
    outputPath = args[i + 1];
    i += 1;
  } else if (!inputPath) {
    inputPath = arg;
  } else {
    printUsage();
    process.exit(2);
  }
}

if (!inputPath) {
  printUsage();
  process.exit(2);
}

const source = await readFile(inputPath, 'utf8');
const ir = parseDSL(source);
const catalog = await loadCatalog();
const verdict = checkIR(ir, catalog);
const manifest = manifestFromVerdict(verdict);
const payload = JSON.stringify(manifest, null, 2) + '\n';

if (outputPath) {
  await mkdir(dirname(outputPath), { recursive: true });
  await writeFile(outputPath, payload, 'utf8');
} else {
  process.stdout.write(payload);
}

process.exit(verdict.ok === false ? 1 : 0);
