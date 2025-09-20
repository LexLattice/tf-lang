#!/usr/bin/env node
import { readFile, writeFile, mkdir } from 'node:fs/promises';
import { dirname } from 'node:path';

import { parseDSL } from '../src/parser.mjs';
import { checkIR } from '../../tf-l0-check/src/check.mjs';
import { manifestFromVerdict } from '../../tf-l0-check/src/manifest.mjs';

async function loadCatalog() {
  try {
    return JSON.parse(
      await readFile('packages/tf-l0-spec/spec/catalog.json', 'utf8')
    );
  } catch {
    return { primitives: [] };
  }
}

const args = process.argv.slice(2);

function usage() {
  console.error('Usage: node packages/tf-compose/bin/tf-manifest.mjs <flow.tf> [-o out.json]');
}

let file = null;
let out = null;

for (let i = 0; i < args.length; i++) {
  const arg = args[i];
  if (arg === '-o' || arg === '--out') {
    out = args[i + 1] || null;
    i++;
    continue;
  }
  if (!file) {
    file = arg;
    continue;
  }
  // unexpected extra positional args
  usage();
  process.exit(2);
}

if (!file) {
  usage();
  process.exit(2);
}

const src = await readFile(file, 'utf8');
const ir = parseDSL(src);
const catalog = await loadCatalog();
const verdict = checkIR(ir, catalog);
const manifest = manifestFromVerdict(verdict);
const payload = JSON.stringify(manifest, null, 2) + '\n';

if (out) {
  await mkdir(dirname(out), { recursive: true });
  await writeFile(out, payload, 'utf8');
} else {
  process.stdout.write(payload);
}

process.exit(verdict.ok === false ? 1 : 0);
