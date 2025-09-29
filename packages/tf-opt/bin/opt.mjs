#!/usr/bin/env node
import { writeFile, mkdir } from 'node:fs/promises';
import { dirname } from 'node:path';
import { readJsonFile } from '../lib/data.mjs';
import { extractPrimitivesFromIr, analyzePrimitiveSequence } from '../lib/rewrite-detect.mjs';

const arg = k => { const i = process.argv.indexOf(k); return i>=0 ? process.argv[i+1] : null; };
if (process.argv.includes('--help')) { console.log('tf-opt --ir <file> [-o out.json] [--cost show] [--emit-used-laws <file>]');
process.exit(0); }

const COST = {
  Pure: 1, Observability: 2, 'Storage.Read': 5, 'Network.Out': 7, 'Storage.Write': 9, Crypto: 8
};

async function main(){
  if (process.argv.includes('--cost') && arg('--cost') === 'show') {
    console.log(JSON.stringify(COST, null, 2));
    return;
  }
  const irPath = arg('--ir');
  const out = arg('-o') || arg('--out');
  const emitUsed = arg('--emit-used-laws');
  const ir = irPath ? await readJsonFile(irPath, {}) : {};
  const seq = extractPrimitivesFromIr(ir);
  const analysis = await analyzePrimitiveSequence(seq);
  const plan = { rewritesApplied: analysis.rewritesApplied, used_laws: analysis.laws };
  const planJson = JSON.stringify(plan, null, 2);
  console.log(planJson);
  const serialized = `${planJson}\n`;
  if (out) { await mkdir(dirname(out), { recursive: true }); await writeFile(out, serialized); }
  if (emitUsed) { await mkdir(dirname(emitUsed), { recursive: true }); await writeFile(emitUsed, serialized); }
}
main().catch(e => { console.error(e); process.exit(1); });
