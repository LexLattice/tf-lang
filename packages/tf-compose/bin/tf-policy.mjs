#!/usr/bin/env node
import { readFile, writeFile, mkdir } from 'node:fs/promises';
import { dirname } from 'node:path';

import { parseDSL } from '../src/parser.mjs';
import { canonicalize } from '../../tf-l0-ir/src/hash.mjs';
import { checkTransactions } from '../../tf-l0-check/src/txn.mjs';

async function loadCatalog() {
  try {
    return JSON.parse(await readFile('packages/tf-l0-spec/spec/catalog.json', 'utf8'));
  } catch {
    return { primitives: [] };
  }
}

const rawArgs = process.argv.slice(2);
const args = rawArgs[0] === '--' ? rawArgs.slice(1) : rawArgs;

function argValue(flag) {
  const idx = args.indexOf(flag);
  if (idx >= 0) return args[idx + 1] ?? null;
  return null;
}

const cmd = args[0];
if (cmd !== 'check') {
  console.error('Usage: tf-policy check <flow.tf> [--forbid-outside] [-o out.json]');
  process.exit(2);
}

const file = args[1];
if (!file) {
  console.error('Missing flow path.');
  process.exit(2);
}

const forbidOutside = args.includes('--forbid-outside');
const out = argValue('-o') || argValue('--out');

const src = await readFile(file, 'utf8');
const ir = parseDSL(src);
const catalog = await loadCatalog();

const verdict = checkTransactions(ir, catalog, { forbidWritesOutsideTxn: forbidOutside });
const payload = canonicalize({ ok: Boolean(verdict.ok), reasons: verdict.reasons || [] }) + '\n';

if (out) {
  await mkdir(dirname(out), { recursive: true });
  await writeFile(out, payload, 'utf8');
} else {
  process.stdout.write(payload);
}

process.exit(verdict.ok ? 0 : 1);
