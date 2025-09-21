#!/usr/bin/env node
import { readFile, writeFile, mkdir } from 'node:fs/promises';
import { dirname, resolve } from 'node:path';
import process from 'node:process';
import { parseArgs } from 'node:util';

import { parseDSL } from '../packages/tf-compose/src/parser.mjs';
import { emitAlloyAuth } from '../packages/tf-l0-proofs/src/alloy-auth.mjs';

async function main(argv) {
  const { values, positionals } = parseArgs({
    args: argv.slice(2),
    options: {
      out: { type: 'string', short: 'o' },
    },
    allowPositionals: true,
  });

  if (positionals.length !== 1) {
    usage('expected exactly one input flow');
    process.exit(2);
  }

  const outPath = typeof values.out === 'string' ? resolve(values.out) : null;
  if (!outPath) {
    usage('missing --out <file>');
    process.exit(2);
  }

  const inputPath = resolve(positionals[0]);
  const ir = await loadIR(inputPath);
  const primIndex = await loadPrimIndex();
  const alloy = emitAlloyAuth(ir, { primIndex });

  await mkdir(dirname(outPath), { recursive: true });
  await writeFile(outPath, ensureTrailingNewline(alloy), 'utf8');
  process.stdout.write(`wrote ${outPath}\n`);
}

function usage(message) {
  if (message) {
    process.stderr.write(`${message}\n`);
  }
  process.stderr.write('Usage: node scripts/emit-alloy-auth.mjs <input.tf|input.ir.json> -o <out.als>\n');
}

async function loadIR(sourcePath) {
  if (sourcePath.endsWith('.tf')) {
    return loadFlow(sourcePath);
  }
  if (sourcePath.endsWith('.ir.json')) {
    const raw = await readFile(sourcePath, 'utf8');
    return JSON.parse(raw);
  }
  throw new Error('unsupported input; expected .tf or .ir.json');
}

async function loadFlow(srcPath) {
  const raw = await readFile(srcPath, 'utf8');
  return parseDSL(raw);
}

async function loadPrimIndex() {
  const [catalog, scopeRules] = await Promise.all([loadCatalog(), loadAuthorizeScopes()]);
  return buildPrimIndex(catalog, scopeRules);
}

async function loadCatalog() {
  const catalogUrl = new URL('../packages/tf-l0-spec/spec/catalog.json', import.meta.url);
  const raw = await readFile(catalogUrl, 'utf8');
  return JSON.parse(raw);
}

async function loadAuthorizeScopes() {
  const scopeUrl = new URL('../packages/tf-l0-check/rules/authorize-scopes.json', import.meta.url);
  const raw = await readFile(scopeUrl, 'utf8');
  return JSON.parse(raw);
}

function buildPrimIndex(catalog, scopeRules) {
  const map = new Map();
  const prims = Array.isArray(catalog?.primitives) ? catalog.primitives : [];
  for (const prim of prims) {
    if (!prim || typeof prim.name !== 'string') {
      continue;
    }
    const key = prim.name.toLowerCase();
    const id = typeof prim.id === 'string' ? prim.id : prim.name;
    const scopes = Array.isArray(scopeRules?.[id]) ? scopeRules[id] : [];
    map.set(key, { id, scopes });
  }
  return map;
}

function ensureTrailingNewline(text) {
  return text.endsWith('\n') ? text : `${text}\n`;
}

main(process.argv).catch((error) => {
  process.stderr.write(`${error?.stack || error}\n`);
  process.exit(1);
});
