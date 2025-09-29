#!/usr/bin/env node
import { writeFile, mkdir } from 'node:fs/promises';
import { dirname } from 'node:path';
import { readJsonFile, isKnownLaw } from '../lib/data.mjs';
import { extractPrimitivesFromIr, analyzePrimitiveSequence } from '../lib/rewrite-detect.mjs';
import { applyRewritePlan, stableStringify } from '../lib/plan-apply.mjs';

const arg = (k) => {
  const index = process.argv.indexOf(k);
  return index >= 0 ? process.argv[index + 1] : null;
};

if (process.argv.includes('--help')) {
  console.log(
    [
      'Usage: tf-opt --ir <file> [--plan-only | --apply --out <file>] [options]',
      '',
      'Options:',
      '  --plan-only               analyze and emit the rewrite plan (default)',
      '  --apply                   apply detected rewrites and emit normalized IR',
      '  --emit-used-laws <file>   write the used laws JSON to <file>',
      '  --out, -o <file>          write primary output JSON to <file>',
      '  --cost show               print the cost table',
      '  --help                    show this message',
    ].join('\n'),
  );
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
  const planOnly = process.argv.includes('--plan-only') || !process.argv.includes('--apply');
  if (planOnly) {
    const plan = buildPlan(ir, analysis);
    const planJson = stableStringify(plan) + '\n';
    process.stdout.write(planJson);
    if (out) {
      await mkdir(dirname(out), { recursive: true });
      await writeFile(out, planJson, 'utf8');
    }
    if (emitUsed) {
      const used = stableStringify({ used_laws: plan.used_laws }) + '\n';
      await mkdir(dirname(emitUsed), { recursive: true });
      await writeFile(emitUsed, used, 'utf8');
    }
    return;
  }

  const applied = applyRewritePlan(ir, analysis.obligations);
  const appliedIr = applied.ir;
  const appliedJson = stableStringify(appliedIr) + '\n';
  process.stdout.write(appliedJson);
  if (out) {
    await mkdir(dirname(out), { recursive: true });
    await writeFile(out, appliedJson, 'utf8');
  }

  const postPrimitives = extractPrimitivesFromIr(appliedIr);
  const postAnalysis = await analyzePrimitiveSequence(postPrimitives);
  const plan = buildPlan(appliedIr, postAnalysis);
  const usedLaws = new Set([...plan.used_laws, ...applied.usedLaws]);
  plan.used_laws = Array.from(usedLaws).sort();
  plan.rewrites_applied = Math.max(plan.rewrites_applied, applied.rewritesApplied);

  if (emitUsed) {
    const used = stableStringify({ used_laws: plan.used_laws }) + '\n';
    await mkdir(dirname(emitUsed), { recursive: true });
    await writeFile(emitUsed, used, 'utf8');
  }
}

function buildPlan(ir, analysis) {
  const lawSet = new Set(Array.isArray(analysis.laws) ? analysis.laws : []);
  const counts = [];
  const baseRewrites = Math.max(
    typeof analysis.rewritesApplied === 'number' ? analysis.rewritesApplied : 0,
    Array.isArray(analysis.obligations) ? analysis.obligations.length : 0,
  );

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

  let rewritesApplied = baseRewrites;
  for (const value of counts) {
    if (typeof value === 'number' && Number.isFinite(value) && value > rewritesApplied) {
      rewritesApplied = value;
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
    if (current == null) {
      continue;
    }
    if (typeof current === 'number') {
      counts.push(current);
      continue;
    }
    if (typeof current === 'string') {
      maybeAddLaw(current, lawSet);
      continue;
    }
    if (Array.isArray(current)) {
      if (contextKey === 'rewrites') {
        counts.push(current.length);
      }
      for (let i = current.length - 1; i >= 0; i -= 1) {
        stack.push({ value: current[i], sourceKey: contextKey });
      }
      continue;
    }
    if (typeof current === 'object') {
      if (typeof current.count === 'number') {
        counts.push(current.count);
      }
      if (typeof current.rewritesApplied === 'number') {
        counts.push(current.rewritesApplied);
      }
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
  if (typeof name !== 'string') {
    return;
  }
  const trimmed = name.trim();
  if (!trimmed) {
    return;
  }
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
