#!/usr/bin/env node
import { readFile, writeFile, mkdir } from 'node:fs/promises';
import { dirname } from 'node:path';

async function loadParser() {
  try {
    const mod = await import('../packages/tf-compose/src/parser.mjs');
    if (typeof mod.parseDSL === 'function') {
      return mod.parseDSL;
    }
  } catch {
    // fall through
  }
  const fallback = await import('../packages/tf-compose/src/parser.with-regions.mjs');
  return fallback.parseDSL;
}

async function main() {
  const args = process.argv.slice(2);
  if (args.length === 0) {
    console.error('Usage: node scripts/emit-smt.mjs <flow.tf> -o out/0.4/proofs/<name>.smt2');
    process.exit(2);
  }

  const flowPath = args[0];
  if (!flowPath || flowPath.startsWith('-')) {
    console.error('Missing flow path.');
    process.exit(2);
  }

  let outPath = null;
  for (let i = 1; i < args.length; i++) {
    const flag = args[i];
    if (flag === '-o' || flag === '--out') {
      outPath = args[i + 1] || null;
      i++;
    }
  }
  if (!outPath) {
    console.error('Missing output path.');
    process.exit(2);
  }

  let src;
  try {
    src = await readFile(flowPath, 'utf8');
  } catch (err) {
    console.error(`Failed to read flow at ${flowPath}: ${err.message}`);
    process.exit(1);
  }

  const parseDSL = await loadParser();
  const { emitSMT } = await import('../packages/tf-l0-proofs/src/smt.mjs');

  let ir;
  try {
    ir = parseDSL(src);
  } catch (err) {
    console.error(`Failed to parse flow: ${err.message}`);
    process.exit(1);
  }

  const smt = emitSMT(ir);

  try {
    await mkdir(dirname(outPath), { recursive: true });
    await writeFile(outPath, smt, 'utf8');
  } catch (err) {
    console.error(`Failed to write SMT file: ${err.message}`);
    process.exit(1);
  }
}

await main();
