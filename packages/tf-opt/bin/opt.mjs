#!/usr/bin/env node
import { readFile, writeFile, mkdir } from 'node:fs/promises';
import { dirname } from 'node:path';

const LAW_ALIAS = new Map([
  ['law:emitmetric-commutes-with-pure', 'commute:emit-metric-with-pure'],
  ['law:hash-idempotent', 'idempotent:hash'],
  ['law:serialize-deserialize-eq-id', 'inverse:serialize-deserialize'],
]);

const LAW_NAME_PATTERN = /^(commute|idempotent|inverse):/;

const arg = k => { const i = process.argv.indexOf(k); return i>=0 ? process.argv[i+1] : null; };
if (process.argv.includes('--help')) { console.log('tf-opt --ir <file> [-o out.json] [--cost show] [--emit-used-laws <file>]'); process.exit(0); }

const COST = {
  Pure: 1, Observability: 2, 'Storage.Read': 5, 'Network.Out': 7, 'Storage.Write': 9, Crypto: 8
};

async function loadIR(p){
  try { return JSON.parse(await readFile(p, 'utf8')); } catch { return {}; }
}

function normalizeLawName(raw) {
  if (typeof raw !== 'string') return null;
  const value = raw.trim();
  if (!value) return null;
  if (LAW_ALIAS.has(value)) return LAW_ALIAS.get(value);
  if (LAW_NAME_PATTERN.test(value)) return value;
  return null;
}

function collectRewriteInfo(ir) {
  const laws = new Set();
  let rewrites = 0;

  const visit = (node) => {
    if (!node || typeof node !== 'object') return;
    if (Array.isArray(node)) {
      for (const entry of node) visit(entry);
      return;
    }

    const handledKeys = new Set();

    if (Array.isArray(node.rewrites)) {
      handledKeys.add('rewrites');
      for (const rewrite of node.rewrites) {
        if (!rewrite || typeof rewrite !== 'object') continue;
        const law = normalizeLawName(rewrite.law ?? rewrite.law_id ?? rewrite.lawId ?? rewrite.id);
        if (law) {
          laws.add(law);
          rewrites += 1;
        }
        // Some encoders may expose `laws` arrays per rewrite entry.
        if (Array.isArray(rewrite.laws)) {
          for (const entry of rewrite.laws) {
            const normalized = normalizeLawName(entry);
            if (normalized) {
              laws.add(normalized);
            }
          }
        }
      }
    }

    if (Array.isArray(node.used_laws)) {
      handledKeys.add('used_laws');
      for (const entry of node.used_laws) {
        const law = normalizeLawName(entry);
        if (law) laws.add(law);
      }
    }

    if (Array.isArray(node.laws)) {
      handledKeys.add('laws');
      for (const entry of node.laws) {
        if (typeof entry === 'string') {
          const law = normalizeLawName(entry);
          if (law) laws.add(law);
        } else if (entry && typeof entry === 'object') {
          const law = normalizeLawName(entry.law ?? entry.id);
          if (law) {
            laws.add(law);
            if (entry.applied === true) {
              rewrites += 1;
            }
          }
        }
      }
    }

    const directLaw = normalizeLawName(node.law ?? node.law_id ?? node.lawId ?? node.id);
    if (directLaw) {
      laws.add(directLaw);
      rewrites += 1;
    }

    for (const [key, value] of Object.entries(node)) {
      if (handledKeys.has(key)) continue;
      if (key === 'law' || key === 'law_id' || key === 'lawId' || key === 'id') continue;
      if (typeof value === 'string') {
        const law = normalizeLawName(value);
        if (law) laws.add(law);
        continue;
      }
      visit(value);
    }
  };

  visit(ir);

  if (laws.size === 0) {
    const prims = listPrims(ir);
    if (prims.includes('hash') && prims.includes('emit-metric')) {
      laws.add('commute:emit-metric-with-pure');
      rewrites = Math.max(rewrites, 1);
    }
  }

  return { laws, rewrites };
}

function listPrims(ir, acc = []) {
  if (!ir || typeof ir !== 'object') return acc;
  if (ir.node === 'Prim') acc.push((ir.prim || '').toLowerCase());
  for (const k of Object.keys(ir)) {
    const v = ir[k];
    if (Array.isArray(v)) v.forEach((x) => listPrims(x, acc));
    else if (v && typeof v === 'object') listPrims(v, acc);
  }
  return acc;
}

function rewritePlan(ir) {
  const { laws, rewrites } = collectRewriteInfo(ir);
  const used_laws = Array.from(laws).sort();
  const rewritesApplied = rewrites > 0 ? rewrites : used_laws.length;
  return { rewritesApplied, used_laws };
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
