#!/usr/bin/env node
import { run } from '../dist/index.js';

function arg(k){ const i = process.argv.indexOf(k); return i>=0 ? process.argv[i+1] : null; }
if (process.argv.includes('--help')) {
  console.log('tf-run-wasm --ir <path> [--status out.json] [--trace out.jsonl]');
  process.exit(0);
}
const irPath = arg('--ir') || 'out/0.4/ir/signing.ir.json';
const statusPath = arg('--status');
const tracePath = arg('--trace');
const { status, trace } = await run({ irPath, statusPath, tracePath });
console.log(`wrote status=${!!statusPath} trace=${!!tracePath} steps=${trace.length}`);
