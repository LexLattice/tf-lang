#!/usr/bin/env node
import { readFile, writeFile, mkdir } from 'node:fs/promises';
import { dirname } from 'node:path';

import { parseDSL } from '../src/parser.mjs';
import { checkTransactions } from '../../tf-l0-check/src/txn.mjs';

async function loadCatalog() {
  try {
    return JSON.parse(await readFile('packages/tf-l0-spec/spec/catalog.json', 'utf8'));
  } catch {
    return { primitives: [] };
  }
}

const args = process.argv.slice(2);
const cmd = args[0];

if (cmd !== 'check') {
  console.error('Usage: tf-policy check <flow.tf> [--forbid-outside] [-o out.json]');
  process.exit(2);
}

const file = args[1];
if (!file || file.startsWith('-')) {
  console.error('Missing flow path.');
  process.exit(2);
}

let forbidOutside = false;
let out = null;

for (let i = 2; i < args.length; i++) {
  const tok = args[i];
  if (tok === '--forbid-outside') {
    forbidOutside = true;
    continue;
  }
  if (tok === '-o' || tok === '--out') {
    const target = args[i + 1];
    if (!target) {
      console.error('Missing value for', tok);
      process.exit(2);
    }
    out = target;
    i++;
    continue;
  }
  console.error('Unknown argument:', tok);
  process.exit(2);
}

let src;
try {
  src = await readFile(file, 'utf8');
} catch (err) {
  console.error('Failed to read flow:', err.message || err);
  process.exit(1);
}

let ir;
try {
  ir = parseDSL(src);
} catch (err) {
  console.error('Failed to parse flow:', err.message || err);
  process.exit(1);
}

const catalog = await loadCatalog();
const verdict = checkTransactions(ir, catalog, { forbidWritesOutsideTxn: forbidOutside });
const payload = JSON.stringify(verdict, ['ok', 'reasons'], 2) + '\n';

if (out) {
  await mkdir(dirname(out), { recursive: true });
  await writeFile(out, payload, 'utf8');
} else {
  process.stdout.write(payload);
}

process.exit(verdict.ok ? 0 : 1);
