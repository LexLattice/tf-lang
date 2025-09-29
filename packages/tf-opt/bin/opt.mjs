#!/usr/bin/env node
import { readFile, writeFile, mkdir } from 'node:fs/promises';
import { dirname } from 'node:path';

import {
  analyzePrimitiveSequence,
  extractPrimitivesFromIr,
} from '../lib/rewrite-detect.mjs';
import { canonicalLawName } from '../lib/data.mjs';

const arg = k => { const i = process.argv.indexOf(k); return i>=0 ? process.argv[i+1] : null; };
if (process.argv.includes('--help')) { console.log('tf-opt --ir <file> [-o out.json] [--cost show] [--emit-used-laws <file>]'); process.exit(0); }

const COST = {
  Pure: 1, Observability: 2, 'Storage.Read': 5, 'Network.Out': 7, 'Storage.Write': 9, Crypto: 8
};

async function loadIR(p){
  try { return JSON.parse(await readFile(p, 'utf8')); } catch { return {}; }
}

function normalizeLawList(entries) {
  const set = new Set();
  for (const entry of Array.isArray(entries) ? entries : []) {
    if (typeof entry === 'string') {
      const law = canonicalLawName(entry);
      if (law) set.add(law);
      continue;
    }
    if (entry && typeof entry === 'object' && typeof entry.law === 'string') {
      const law = canonicalLawName(entry.law);
      if (law) set.add(law);
    }
  }
  return set;
}

async function rewritePlan(ir) {
  const primitives = extractPrimitivesFromIr(ir);
  const analysis = await analyzePrimitiveSequence(primitives);
  const summary = analysis.summary ?? { laws: analysis.laws, rewritesApplied: analysis.rewritesApplied };
  const usedLawSet = normalizeLawList(summary.laws);
  for (const law of Array.isArray(analysis.laws) ? analysis.laws : []) {
    const canonical = canonicalLawName(law);
    if (canonical) {
      usedLawSet.add(canonical);
    }
  }

  const rewrites = [];
  for (const entry of Array.isArray(analysis.obligations) ? analysis.obligations : []) {
    const law = canonicalLawName(entry?.law ?? '');
    const rewrite = typeof entry?.rewrite === 'string' ? entry.rewrite.trim() : '';
    if (!law || !rewrite) {
      continue;
    }
    rewrites.push({ law, rewrite });
    usedLawSet.add(law);
  }
  rewrites.sort((a, b) => {
    const left = a.rewrite.localeCompare(b.rewrite);
    return left !== 0 ? left : a.law.localeCompare(b.law);
  });

  const usedLaws = Array.from(usedLawSet).sort((a, b) => a.localeCompare(b));
  return {
    primitiveSequence: analysis.primitives,
    rewrites,
    rewritesApplied: summary.rewritesApplied ?? analysis.rewritesApplied,
    laws: usedLaws,
    used_laws: usedLaws,
  };
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
  const plan = await rewritePlan(ir);
  const planJson = JSON.stringify(plan, null, 2);
  console.log(planJson);
  if (out) {
    await mkdir(dirname(out), { recursive: true });
    await writeFile(out, `${planJson}\n`);
  }
  if (emitUsed) {
    const used = {
      used_laws: plan.used_laws,
    };
    if (plan.rewrites.length > 0) {
      used.rewrites = plan.rewrites;
    }
    await mkdir(dirname(emitUsed), { recursive: true });
    await writeFile(emitUsed, `${JSON.stringify(used, null, 2)}\n`);
  }
}
main().catch(e => { console.error(e); process.exit(1); });
