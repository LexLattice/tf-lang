#!/usr/bin/env node
import { writeFile, mkdir } from 'node:fs/promises';
import { dirname } from 'node:path';
import { readJsonFile, isKnownLaw } from '../lib/data.mjs';
import { extractPrimitivesFromIr, analyzePrimitiveSequence } from '../lib/rewrite-detect.mjs';

const arg = (k) => {
  const i = process.argv.indexOf(k);
  return i >= 0 ? process.argv[i + 1] : null;
};

if (process.argv.includes('--help')) {
  console.log('tf-opt --ir <file> [--cost show] [-o out.json] [--emit-used-laws <file>]');
  process.exit(0);
}

const COST = {
  Pure: 1,
  Observability: 2,
  'Storage.Read': 5,
  'Network.Out': 7,
  'Storage.Write': 9,
  Crypto: 8,
};

async function main() {
  if (process.argv.includes('--cost') && arg('--cost') === 'show') {
    console.log(JSON.stringify(COST, null, 2));
    return;
  }

  const irPath = arg('--ir');
  const out = arg('-o') || arg('--out');
  const emitUsed = arg('--emit-used-laws');

  const ir = irPath ? await readJsonFile(irPath, {}) : {};
  const primitives = extractPrimitivesFromIr(ir);
  const analysis = await analyzePrimitiveSequence(primitives);

  const plan = buildPlan(ir, analysis);

  const planJson = JSON.stringify(plan, null, 2) + '\n';
  process.stdout.write(planJson);

  if (out) {
    await mkdir(dirname(out), { recursive: true });
    await writeFile(out, planJson, 'utf8');
  }
  if (emitUsed) {
    const used = JSON.stringify({ used_laws: plan.used_laws }, null, 2) + '\n';
    await mkdir(dirname(emitUsed), { recursive: true });
    await writeFile(emitUsed, used, 'utf8');
  }
}

/**
 * Build a deterministic plan from analyzer output, optionally
 * augmenting with IR-level metadata (rewrites / used_laws / laws).
 */
function buildPlan(ir, analysis) {
  // Start from analyzer facts
  const lawSet = new Set(Array.isArray(analysis.laws) ? analysis.laws : []);
  const counts = [];

  const baseRewrites = Math.max(
    typeof analysis.rewritesApplied === 'number' ? analysis.rewritesApplied : 0,
    Array.isArray(analysis.obligations) ? analysis.obligations.length : 0,
  );

  // Optionally merge IR-provided metadata (forward-compatible)
  if (ir && typeof ir === 'object') {
    if (Object.prototype.hasOwnProperty.call(ir, 'rewrites')) {
      collectMetadata(ir.rewrites, 'rewrites', lawSet, counts);
    }
    if (Object.prototype.hasOwnProperty.call(ir, 'used_laws')) {
      collectMetadata(ir.used_laws, 'used_laws', lawSet, counts);
    }
    if (Object.prototype.hasOwnProperty.call(ir, 'laws')) {
      collectMetadata(ir.laws, 'laws', lawSet, counts);
    }
  }

  // Pick the largest declared/observed count
  let rewritesApplied = baseRewrites;
  for (const v of counts) {
    if (typeof v === 'number' && Number.isFinite(v) && v > rewritesApplied) {
      rewritesApplied = v;
    }
  }

  return {
    rewrites_applied: rewritesApplied,
    used_laws: Array.from(lawSet).sort(),
  };
}

function collectMetadata(value, sourceKey, lawSet, counts) {
  const stack = [{ value, sourceKey }];
  while (stack.length > 0) {
    const { value: current, sourceKey: contextKey } = stack.pop();

    if (current == null) continue;

    if (typeof current === 'number') {
      counts.push(current);
      continue;
    }

    if (typeof current === 'string') {
      maybeAddLaw(current, lawSet);
      continue;
    }

    if (Array.isArray(current)) {
      if (contextKey === 'rewrites') counts.push(current.length);
      for (let i = current.length - 1; i >= 0; i -= 1) {
        stack.push({ value: current[i], sourceKey: contextKey });
      }
      continue;
    }

    if (typeof current === 'object') {
      if (typeof current.count === 'number') counts.push(current.count);
      if (typeof current.rewritesApplied === 'number') counts.push(current.rewritesApplied);

      for (const key of ['law', 'id', 'name']) {
        if (typeof current[key] === 'string') {
          maybeAddLaw(current[key], lawSet);
        }
      }

      for (const nextKey of ['laws', 'used_laws', 'rewrites']) {
        if (Object.prototype.hasOwnProperty.call(current, nextKey)) {
          stack.push({ value: current[nextKey], sourceKey: nextKey });
        }
      }

      for (const [key, val] of Object.entries(current)) {
        if (
          key === 'count' ||
          key === 'rewritesApplied' ||
          key === 'law' ||
          key === 'id' ||
          key === 'name' ||
          key === 'laws' ||
          key === 'used_laws' ||
          key === 'rewrites'
        ) {
          continue;
        }
        if (isLikelyLawName(key)) {
          maybeAddLaw(key, lawSet);
          if (typeof val === 'number') {
            counts.push(val);
            continue;
          }
        }
        stack.push({ value: val, sourceKey: key });
      }
    }
  }
}

function maybeAddLaw(name, lawSet) {
  if (typeof name !== 'string') return;
  const trimmed = name.trim();
  if (!trimmed) return;
  if (isKnownLaw(trimmed) || trimmed.includes(':')) {
    lawSet.add(trimmed);
  }
}

function isLikelyLawName(name) {
  return typeof name === 'string' && (isKnownLaw(name) || name.includes(':'));
}

main().catch((error) => {
  console.error(error);
  process.exit(1);
});
