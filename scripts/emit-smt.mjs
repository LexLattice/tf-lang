#!/usr/bin/env node
import { readFile, writeFile, mkdir } from 'node:fs/promises';
import { basename, dirname, extname } from 'node:path';
import process from 'node:process';

import { parseDSL } from '../packages/tf-compose/src/parser.mjs';
import { checkIR } from '../packages/tf-l0-check/src/check.mjs';
import { emitSMT } from '../packages/tf-l0-proofs/src/smt.mjs';

async function loadCatalog() {
  try {
    const catalogUrl = new URL('../packages/tf-l0-spec/spec/catalog.json', import.meta.url);
    const raw = await readFile(catalogUrl, 'utf8');
    return JSON.parse(raw);
  } catch {
    return { primitives: [] };
  }
}

function annotateWrites(node, catalog) {
  if (!node || typeof node !== 'object' || node === null) {
    return;
  }
  try {
    const verdict = checkIR(node, catalog) || {};
    node.writes = Array.isArray(verdict.writes) ? verdict.writes : [];
  } catch {
    node.writes = Array.isArray(node.writes) ? node.writes : [];
  }
  if (Array.isArray(node.children)) {
    for (const child of node.children) {
      annotateWrites(child, catalog);
    }
  }
}

function usage() {
  console.error('Usage: node scripts/emit-smt.mjs <flow.tf> [-o <out.smt2>]');
}

const args = process.argv.slice(2);
if (args.length === 0) {
  usage();
  process.exit(1);
}

const flowPath = args[0];
let outPath = null;
for (let i = 1; i < args.length; i++) {
  const arg = args[i];
  if (arg === '-o' || arg === '--out') {
    outPath = args[i + 1] || null;
    i++;
  }
}

const defaultOut = () => {
  const base = basename(flowPath, extname(flowPath) || undefined) || 'flow';
  return `out/0.4/proofs/${base}.smt2`;
};

try {
  const source = await readFile(flowPath, 'utf8');
  const ir = parseDSL(source);
  const catalog = await loadCatalog();
  annotateWrites(ir, catalog);
  const smt = emitSMT(ir);
  const target = outPath || defaultOut();
  await mkdir(dirname(target), { recursive: true });
  await writeFile(target, smt, 'utf8');
} catch (err) {
  console.error(err instanceof Error ? err.message : String(err));
  process.exit(1);
}
