#!/usr/bin/env node
import { readFile, writeFile, mkdir } from 'node:fs/promises';
import { dirname } from 'node:path';

import { parseDSL } from '../src/parser.mjs';
import { checkTransactions } from '../../tf-l0-check/src/txn.mjs';

async function loadCatalog() {
  try {
    const raw = await readFile('packages/tf-l0-spec/spec/catalog.json', 'utf8');
    return JSON.parse(raw);
  } catch {
    return { primitives: [] };
  }
}

const rawArgs = process.argv.slice(2);
const args = rawArgs[0] === '--' ? rawArgs.slice(1) : rawArgs;

function arg(name) {
  const idx = args.indexOf(name);
  return idx >= 0 ? args[idx + 1] : null;
}

function hasFlag(name) {
  return args.includes(name);
}

const cmd = args[0];
if (!cmd || cmd !== 'check') {
  console.error('Usage: tf-policy check <flow.tf> [--forbid-outside] [-o out.json]');
  process.exit(2);
}

const file = args[1];
if (!file) {
  console.error('Missing flow path.');
  process.exit(2);
}

const out = arg('-o') || arg('--out');
const forbidOutside = hasFlag('--forbid-outside');

const src = await readFile(file, 'utf8');
const ir = parseDSL(src);
const catalog = await loadCatalog();

const verdict = checkTransactions(ir, catalog, {
  forbidWritesOutsideTxn: forbidOutside
});

const payload = JSON.stringify({ ok: verdict.ok, reasons: verdict.reasons || [] }, null, 2) + '\n';

if (out) {
  await mkdir(dirname(out), { recursive: true });
  await writeFile(out, payload, 'utf8');
} else {
  process.stdout.write(payload);
}

process.exit(verdict.ok ? 0 : 1);
