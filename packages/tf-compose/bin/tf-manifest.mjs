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

const args = process.argv.slice(2);

if (args.length === 0 || args.includes('--help') || args.includes('-h')) {
  console.error('Usage: node packages/tf-compose/bin/tf-manifest.mjs <flow.tf> [-o out.json]');
  process.exit(2);
}

let file = null;
let out = null;
for (let i = 0; i < args.length; i += 1) {
  const arg = args[i];
  if (arg === '-o' || arg === '--out') {
    out = args[i + 1];
    if (!out) {
      console.error('Missing value for', arg);
      process.exit(2);
    }
    i += 1;
  } else if (!file) {
    file = arg;
  } else {
    console.error('Unexpected argument:', arg);
    process.exit(2);
  }
}

if (!file) {
  console.error('Missing flow path.');
  process.exit(2);
}

const src = await readFile(file, 'utf8');
const ir = parseDSL(src);
const cat = await loadCatalog();
const verdict = checkIR(ir, cat);
const manifest = manifestFromVerdict(verdict);
const payload = JSON.stringify(manifest, null, 2) + '\n';

if (out) {
  await mkdir(dirname(out), { recursive: true });
  await writeFile(out, payload, 'utf8');
} else {
  process.stdout.write(payload);
}

process.exit(verdict?.ok === false ? 1 : 0);
