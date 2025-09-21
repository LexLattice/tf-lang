#!/usr/bin/env node
import { readFile, writeFile, mkdir } from 'node:fs/promises';
import { basename, dirname, extname, resolve } from 'node:path';
import process from 'node:process';
import { parseArgs } from 'node:util';

import { parseDSL } from '../packages/tf-compose/src/parser.mjs';
import { emitAlloy } from '../packages/tf-l0-proofs/src/alloy.mjs';

async function main(argv) {
  const { values, positionals } = parseArgs({
    args: argv.slice(2),
    options: { out: { type: 'string', short: 'o' } },
    allowPositionals: true
  });

  if (positionals.length !== 1) {
    usage();
    process.exit(1);
  }

  const inputPath = positionals[0];
  const outputArg = values.out ?? defaultOut(inputPath);
  const srcPath = resolve(inputPath);
  const outPath = resolve(outputArg);

  const ir = await loadIR(srcPath);
  const alloy = emitAlloy(ir);

  await mkdir(dirname(outPath), { recursive: true });
  await writeFile(outPath, alloy, 'utf8');
  process.stdout.write(`wrote ${outPath}\n`);
}

function usage() {
  process.stderr.write(
    'Usage: node scripts/emit-alloy.mjs <input.ir.json|input.tf> [-o out/0.4/proofs/<name>.als>]\n'
  );
}

function defaultOut(inputPath) {
  const base = basename(inputPath);
  if (base.endsWith('.ir.json')) {
    const stem = base.slice(0, -'.ir.json'.length);
    return `out/0.4/proofs/${stem}.als`;
  }
  const ext = extname(base);
  const stem = ext ? base.slice(0, -ext.length) : base;
  return `out/0.4/proofs/${stem}.als`;
}

async function loadIR(srcPath) {
  if (srcPath.endsWith('.ir.json')) {
    const raw = await readFile(srcPath, 'utf8');
    return JSON.parse(raw);
  }
  if (srcPath.endsWith('.tf')) {
    const [raw, catalog] = await Promise.all([readFile(srcPath, 'utf8'), loadCatalog()]);
    const ir = parseDSL(raw);
    annotateWrites(ir, catalog);
    return ir;
  }
  throw new Error('Unsupported input format; expected .ir.json or .tf');
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
    if (node.node === 'Prim') {
      const primName = typeof node.prim === 'string' ? node.prim.toLowerCase() : '';
      const prim = index.get(primName);
      if (!prim) {
        return;
      }
      const concretized = concretizeWrites(prim.writes, node.args);
      if (concretized.length > 0) {
        node.writes = concretized;
      }
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
