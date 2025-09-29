#!/usr/bin/env node
import { writeFile, mkdir } from 'node:fs/promises';
import { dirname } from 'node:path';
import { readJsonFile, isKnownLaw } from '../lib/data.mjs';
import { extractPrimitivesFromIr, analyzePrimitiveSequence } from '../lib/rewrite-detect.mjs';
import {
  stableStringify,
  normalizeRewriteEntries,
  buildUsedLawManifest,
} from '../lib/utils.mjs';
let applyRewritePlanCached = null;

const arg = (k) => {
  const i = process.argv.indexOf(k);
  return i >= 0 ? process.argv[i + 1] : null;
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
      '  --help                    show this message'
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

async function getApplyRewritePlan() {
  if (!applyRewritePlanCached) {
    const mod = await import('../lib/plan-apply.mjs');
    if (!mod || typeof mod.applyRewritePlan !== 'function') {
      throw new Error('applyRewritePlan export missing from plan-apply module');
    }
    applyRewritePlanCached = mod.applyRewritePlan;
  }
  return applyRewritePlanCached;
}

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

  const initialPlan = buildPlan(ir, analysis);

  const planOnly = process.argv.includes('--plan-only') || !process.argv.includes('--apply');
  if (planOnly) {
    const planJson = stableStringify(initialPlan) + '\n';
    process.stdout.write(planJson);
    if (out) {
      await mkdir(dirname(out), { recursive: true });
      await writeFile(out, planJson, 'utf8');
    }
    if (emitUsed) {
      const manifest = buildUsedLawManifest({
        plans: [initialPlan],
      });
      const used = stableStringify(manifest) + '\n';
      await mkdir(dirname(emitUsed), { recursive: true });
      await writeFile(emitUsed, used, 'utf8');
    }
    return;
  }

  // --apply flow
  const applyRewritePlan = await getApplyRewritePlan();
  const applied = applyRewritePlan(ir, analysis.obligations || []);
  const appliedIr = applied.ir;
  const appliedJson = stableStringify(appliedIr) + '\n';
  process.stdout.write(appliedJson);
  if (out) {
    await mkdir(dirname(out), { recursive: true });
    await writeFile(out, appliedJson, 'utf8');
  }

  // Post-apply analysis (for used_laws emission)
  const postPrimitives = extractPrimitivesFromIr(appliedIr);
  const postAnalysis = await analyzePrimitiveSequence(postPrimitives);
  const postPlan = buildPlan(appliedIr, postAnalysis);
  if (emitUsed) {
    const manifest = buildUsedLawManifest({
      plans: [initialPlan, postPlan],
      extras: [applied.usedLaws || []],
    });
    const used = stableStringify(manifest) + '\n';
    await mkdir(dirname(emitUsed), { recursive: true });
    await writeFile(emitUsed, used, 'utf8');
  }
}

/**
 * Build a deterministic plan from analyzer output, optionally
 * augmenting with IR-level metadata (rewrites / used_laws / laws).
 */
function buildPlan(ir, analysis = {}) {
  const counts = [];
  const lawNames = [];

  const rewrites = collectRewritesFromAnalysis(analysis);

  const trackLaw = (name) => {
    if (typeof name === 'string') {
      lawNames.push(name);
    }
  };

  if (Array.isArray(analysis.laws)) {
    for (const law of analysis.laws) trackLaw(law);
  }
  if (Array.isArray(analysis.obligations)) {
    for (const ob of analysis.obligations) {
      if (ob && typeof ob.law === 'string') trackLaw(ob.law);
    }
  }

  if (ir && typeof ir === 'object') {
    collectMetadata({ value: ir, sourceKey: 'root', parentKey: '' }, trackLaw, counts);
  }

  const baseRewrites = Math.max(
    typeof analysis.rewritesApplied === 'number' ? analysis.rewritesApplied : 0,
    Array.isArray(analysis.obligations) ? analysis.obligations.length : 0,
  );

  let rewritesApplied = baseRewrites;
  for (const v of counts) {
    if (typeof v === 'number' && Number.isFinite(v) && v > rewritesApplied) {
      rewritesApplied = v;
    }
  }

  const plan = {
    rewrites_applied: rewritesApplied,
    used_laws: ensureKnownLaws(lawNames),
  };

  if (rewrites.length > 0) {
    plan.rewrites = rewrites;
  }

  return plan;
}

function collectRewritesFromAnalysis(analysis = {}) {
  if (!analysis || typeof analysis !== 'object') return [];

  const entries = [];
  if (Array.isArray(analysis.obligations)) {
    entries.push(...analysis.obligations);
  }
  if (Array.isArray(analysis.rewrites)) {
    entries.push(...analysis.rewrites);
  }

  return normalizeRewriteEntries(entries);
}

function collectMetadata(initialEntry, trackLaw, counts) {
  const stack = [initialEntry];
  while (stack.length > 0) {
    const { value, sourceKey, parentKey } = stack.pop();
    if (value == null) continue;

    if (typeof value === 'number') {
      counts.push(value);
      continue;
    }
    if (typeof value === 'string') {
      if (shouldTrackString(sourceKey, parentKey)) trackLaw(value);
      continue;
    }
    if (Array.isArray(value)) {
      if (sourceKey === 'rewrites') counts.push(value.length);
      for (let i = value.length - 1; i >= 0; i -= 1) {
        stack.push({ value: value[i], sourceKey, parentKey: sourceKey });
      }
      continue;
    }
    if (typeof value === 'object') {
      if (typeof value.count === 'number') counts.push(value.count);
      if (typeof value.rewritesApplied === 'number') counts.push(value.rewritesApplied);
      if (typeof value.law === 'string') trackLaw(value.law);

      if (sourceKey === 'laws' || sourceKey === 'used_laws' || sourceKey === 'rewrites') {
        if (typeof value.name === 'string') trackLaw(value.name);
        if (typeof value.id === 'string') trackLaw(value.id);
      }

      for (const [key, next] of Object.entries(value)) {
        stack.push({ value: next, sourceKey: key, parentKey: sourceKey });
      }
    }
  }
}

function shouldTrackString(sourceKey, parentKey) {
  if (sourceKey === 'laws' || sourceKey === 'used_laws' || sourceKey === 'rewrites') return true;
  if (sourceKey === 'law') return true;
  if ((sourceKey === 'id' || sourceKey === 'name') && (parentKey === 'laws' || parentKey === 'used_laws' || parentKey === 'rewrites')) {
    return true;
  }
  return false;
}

function ensureKnownLaws(laws) {
  const seen = new Set();
  const unknown = new Set();
  for (const law of laws || []) {
    if (typeof law !== 'string') continue;
    const trimmed = law.trim();
    if (!trimmed) continue;
    if (!isKnownLaw(trimmed)) {
      unknown.add(trimmed);
      continue;
    }
    seen.add(trimmed);
  }
  if (unknown.size > 0) {
    throw new Error(`unknown law(s): ${Array.from(unknown).sort().join(', ')}`);
  }
  return Array.from(seen).sort();
}

main().catch((error) => {
  console.error(error instanceof Error ? error.message : String(error));
  process.exit(1);
});
