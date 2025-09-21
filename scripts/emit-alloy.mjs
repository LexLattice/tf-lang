#!/usr/bin/env node
import { readFile, writeFile, mkdir } from 'node:fs/promises';
import { dirname, resolve } from 'node:path';
import process from 'node:process';
import { parseArgs } from 'node:util';

import { parseDSL } from '../packages/tf-compose/src/parser.mjs';
import { emitAlloy } from '../packages/tf-l0-proofs/src/alloy.mjs';

async function main(argv) {
  const { values, positionals } = parseArgs({
    args: argv.slice(2),
    options: {
      out: { type: 'string', short: 'o' },
      scope: { type: 'string' }
    },
    allowPositionals: true
  });

  if (positionals.length !== 1 || typeof values.out !== 'string') {
    usage();
    process.exit(2);
  }

  const inputPath = positionals[0];
  const outPath = resolve(values.out);
  const scope = parseScope(values.scope);

  const ir = await loadIR(resolve(inputPath));
  const alloy = emitAlloy(ir, scope === null ? {} : { scope });

  await mkdir(dirname(outPath), { recursive: true });
  await writeFile(outPath, alloy, 'utf8');
  process.stdout.write(`wrote ${outPath}\n`);
}

function usage() {
  process.stderr.write(
    'Usage: node scripts/emit-alloy.mjs <input.ir.json|input.tf> -o <out.als> [--scope N]\n'
  );
}

function parseScope(raw) {
  if (raw === undefined) {
    return null;
  }
  const value = Number.parseInt(raw, 10);
  if (!Number.isFinite(value) || value <= 0) {
    process.stderr.write('scope must be a positive integer\n');
    process.exit(1);
  }
  return value;
}

async function loadIR(srcPath) {
  if (srcPath.endsWith('.tf')) {
    const [ir, catalog] = await Promise.all([loadFlow(srcPath), loadCatalog()]);
    annotateWrites(ir, catalog);
    return ir;
  }
  if (srcPath.endsWith('.ir.json')) {
    const raw = await readFile(srcPath, 'utf8');
    const ir = JSON.parse(raw);
    const catalog = await loadCatalog();
    annotateWrites(ir, catalog);
    return ir;
  }
  throw new Error('unsupported input; expected .tf or .ir.json');
}

async function loadFlow(srcPath) {
  const raw = await readFile(srcPath, 'utf8');
  return parseDSL(raw);
}

async function loadCatalog() {
  const catalogUrl = new URL('../packages/tf-l0-spec/spec/catalog.json', import.meta.url);
  const raw = await readFile(catalogUrl, 'utf8');
  return JSON.parse(raw);
}

function annotateWrites(ir, catalog) {
  const index = buildCatalogIndex(catalog);
  walk(ir, (node) => {
    if (!node || typeof node !== 'object') {
      return;
    }
    if (node.node !== 'Prim') {
      return;
    }
    if (Array.isArray(node.writes) && node.writes.length > 0) {
      return;
    }
    const primName = typeof node.prim === 'string' ? node.prim.toLowerCase() : '';
    const prim = index.get(primName);
    if (!prim) {
      return;
    }
    const concretized = concretizeWrites(prim.writes, node.args);
    if (concretized.length > 0) {
      node.writes = concretized;
    }
  });
}

function buildCatalogIndex(catalog = {}) {
  const index = new Map();
  for (const prim of catalog.primitives || []) {
    if (prim && typeof prim.name === 'string') {
      index.set(prim.name.toLowerCase(), prim);
    }
  }
  return index;
}

function concretizeWrites(writes = [], args = {}) {
  if (!Array.isArray(writes) || writes.length === 0) {
    return [];
  }
  const seen = new Set();
  const result = [];
  for (const entry of writes) {
    const uri = concretizeUri(entry?.uri, args);
    if (!uri || seen.has(uri)) {
      continue;
    }
    seen.add(uri);
    result.push({ ...entry, uri });
  }
  result.sort((a, b) => a.uri.localeCompare(b.uri));
  return result;
}

function concretizeUri(uri, args = {}) {
  if (isConcreteUri(uri)) {
    return uri;
  }
  const fromArgs = selectUriFromArgs(args);
  return isConcreteUri(fromArgs) ? fromArgs : null;
}

function isConcreteUri(uri) {
  return typeof uri === 'string' && uri.length > 0 && uri !== 'res://unknown' && !/[<>]/.test(uri);
}

function selectUriFromArgs(args = {}) {
  if (!args || typeof args !== 'object') {
    return null;
  }
  const keys = ['uri', 'resource_uri', 'bucket_uri'];
  for (const key of keys) {
    const value = args[key];
    if (typeof value === 'string' && value.length > 0) {
      return value;
    }
  }
  return null;
}

function walk(node, visit) {
  if (!node || typeof node !== 'object') {
    return;
  }
  visit(node);
  if (Array.isArray(node.children)) {
    for (const child of node.children) {
      walk(child, visit);
    }
  }
}

main(process.argv).catch((err) => {
  process.stderr.write(String(err?.stack || err));
  process.stderr.write('\n');
  process.exit(1);
});
