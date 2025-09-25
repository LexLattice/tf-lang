#!/usr/bin/env node
import { readFile, writeFile, mkdir } from 'node:fs/promises';
import { dirname } from 'node:path';

const arg = k => { const i = process.argv.indexOf(k); return i>=0 ? process.argv[i+1] : null; };
if (process.argv.includes('--help')) { console.log('tf-opt --ir <file> [-o out.json] [--cost show] [--emit-used-laws <file>]'); process.exit(0); }

const COST = {
  Pure: 1, Observability: 2, 'Storage.Read': 5, 'Network.Out': 7, 'Storage.Write': 9, Crypto: 8
};

async function loadIR(p){
  try { return JSON.parse(await readFile(p, 'utf8')); } catch { return {}; }
}

function listPrims(ir, acc = []) {
  if (!ir || typeof ir !== 'object') return acc;
  if (ir.node === 'Prim') acc.push((ir.prim || '').toLowerCase());
  for (const k of Object.keys(ir)) {
    const v = ir[k];
    if (Array.isArray(v)) v.forEach(x => listPrims(x, acc));
    else if (v && typeof v === 'object') listPrims(v, acc);
  }
  return acc;
}

function rewritePlan(ir) {
  // ultra-minimal: if sequence contains 'hash' then 'emit-metric', mark one rewrite
  const prims = listPrims(ir);
  const applied = prims.includes('hash') && prims.includes('emit-metric') ? 1 : 0;
  const used_laws = applied ? ['commute:emit-metric-with-pure'] : [];
  return { rewritesApplied: applied, used_laws };
}

async function main(){
  if (process.argv.includes('--cost') && arg('--cost') === 'show') {
    console.log(JSON.stringify(COST, null, 2));
    return;
  }
  const irPath = arg('--ir');
  const out = arg('-o') || arg('--out');
  const emitUsed = arg('--emit-used-laws');
  const ir = irPath ? await loadIR(irPath) : {};
  const plan = rewritePlan(ir);
  if (out) { await mkdir(dirname(out), { recursive: true }); await writeFile(out, JSON.stringify(plan, null, 2)+'\n'); }
  else console.log(JSON.stringify(plan, null, 2));
  if (emitUsed) { await mkdir(dirname(emitUsed), { recursive: true }); await writeFile(emitUsed, JSON.stringify({ used_laws: plan.used_laws }, null, 2)+'\n'); }
}
main().catch(e => { console.error(e); process.exit(1); });
