#!/usr/bin/env node
import { writeFile, mkdir } from 'node:fs/promises';
import { dirname, resolve } from 'node:path';
import { pathToFileURL } from 'node:url';
import { readJsonFile, isKnownLaw } from '../lib/data.mjs';
import { extractPrimitivesFromIr, analyzePrimitiveSequence } from '../lib/rewrite-detect.mjs';
import {
  stableStringify,
  normalizeRewriteEntries,
  buildUsedLawManifest,
} from '../lib/utils.mjs';
let applyRewritePlanCached = null;

const PLAN_STRINGIFY_OPTIONS = {
  keyOrder: {
    '': ['rewrites_applied', 'used_laws', 'rewrites'],
  },
};

const MANIFEST_STRINGIFY_OPTIONS = {
  keyOrder: {
    '': ['used_laws', 'rewrites'],
  },
};

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
    const planJson = stableStringify(initialPlan, PLAN_STRINGIFY_OPTIONS) + '\n';
    process.stdout.write(planJson);
    if (out) {
      await mkdir(dirname(out), { recursive: true });
      await writeFile(out, planJson, 'utf8');
    }
    if (emitUsed) {
      const manifest = buildUsedLawManifest({
        plans: [initialPlan],
      });
      const used = stableStringify(manifest, MANIFEST_STRINGIFY_OPTIONS) + '\n';
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
    const used = stableStringify(manifest, MANIFEST_STRINGIFY_OPTIONS) + '\n';
    await mkdir(dirname(emitUsed), { recursive: true });
    await writeFile(emitUsed, used, 'utf8');
  }
}

/**
 * Build a deterministic plan from analyzer output, optionally
 * augmenting with IR-level metadata (rewrites / used_laws / laws).
 */
function buildPlan(ir, analysis = {}) {
  const analysisMeta = collectPlanMetadata(analysis);
  const irMeta = collectPlanMetadata(ir);

  const combinedRewrites = normalizeRewriteEntries([
    ...analysisMeta.rewrites,
    ...irMeta.rewrites,
  ]);

  const plan = {};
  plan.rewrites_applied = resolveRewriteCount([
    ...analysisMeta.counts,
    ...irMeta.counts,
  ]);
  plan.used_laws = ensureKnownLaws([
    ...analysisMeta.laws,
    ...irMeta.laws,
  ]);

  if (combinedRewrites.length > 0) {
    plan.rewrites = combinedRewrites;
  }

  return plan;
}

function collectPlanMetadata(source) {
  if (!source || typeof source !== 'object') {
    return { laws: [], rewrites: [], counts: [] };
  }

  const laws = [];
  const rewrites = [];
  const counts = [];

  const LAW_COLLECTION_KEYS = new Set(['laws', 'used_laws', 'usedLaws']);
  const REWRITE_ARRAY_KEYS = new Set(['rewrites', 'obligations']);
  const REWRITE_COUNT_KEYS = new Set(['rewrites_applied', 'rewritesApplied']);

  const pushLaw = (law) => {
    if (typeof law !== 'string') return null;
    const trimmed = law.trim();
    if (!trimmed) return null;
    laws.push(trimmed);
    return trimmed;
  };

  const pushRewrite = (law, rewrite) => {
    const normalizedLaw = pushLaw(law);
    if (!normalizedLaw || typeof rewrite !== 'string') return;
    const normalizedRewrite = rewrite.trim();
    if (!normalizedRewrite) return;
    rewrites.push({ law: normalizedLaw, rewrite: normalizedRewrite });
  };

  const enqueueIterable = (iterable, key) => {
    if (!iterable) return;
    for (const item of iterable) {
      if (typeof item === 'string') {
        pushLaw(item);
      } else if (item && typeof item === 'object') {
        for (const candidate of ['law', 'id', 'name']) {
          if (typeof item[candidate] === 'string') {
            pushLaw(item[candidate]);
          }
        }
        if (typeof item.rewrite === 'string' && typeof item.law === 'string') {
          pushRewrite(item.law, item.rewrite);
        }
      }
    }
  };

  const stack = [{ value: source, key: '', parentKey: '' }];
  while (stack.length > 0) {
    const { value, key, parentKey } = stack.pop();
    if (value == null) continue;

    if (typeof value === 'string') {
      if (key === 'law' || LAW_COLLECTION_KEYS.has(parentKey)) {
        pushLaw(value);
      } else if ((key === 'id' || key === 'name') && LAW_COLLECTION_KEYS.has(parentKey)) {
        pushLaw(value);
      }
      continue;
    }

    if (typeof value === 'number') {
      if (REWRITE_COUNT_KEYS.has(key) || (key === 'count' && REWRITE_ARRAY_KEYS.has(parentKey))) {
        counts.push(value);
      }
      continue;
    }

    if (Array.isArray(value) || value instanceof Set) {
      const entries = value instanceof Set ? Array.from(value) : value;
      if (REWRITE_ARRAY_KEYS.has(key)) {
        counts.push(entries.length);
      }
      if (LAW_COLLECTION_KEYS.has(key)) {
        enqueueIterable(entries, key);
      }
      for (let i = entries.length - 1; i >= 0; i -= 1) {
        stack.push({ value: entries[i], key: '', parentKey: key });
      }
      continue;
    }

    if (typeof value === 'object') {
      if (typeof value.law === 'string' && typeof value.rewrite === 'string') {
        pushRewrite(value.law, value.rewrite);
      }
      if (typeof value.rewrites_applied === 'number') {
        counts.push(value.rewrites_applied);
      }
      if (typeof value.rewritesApplied === 'number') {
        counts.push(value.rewritesApplied);
      }
      if (LAW_COLLECTION_KEYS.has(key)) {
        enqueueIterable([value], key);
      }
      for (const [childKey, childValue] of Object.entries(value)) {
        if (LAW_COLLECTION_KEYS.has(childKey)) {
          if (Array.isArray(childValue) || childValue instanceof Set) {
            enqueueIterable(childValue instanceof Set ? Array.from(childValue) : childValue, childKey);
          } else if (childValue && typeof childValue === 'object') {
            for (const candidate of ['law', 'id', 'name']) {
              if (typeof childValue[candidate] === 'string') {
                pushLaw(childValue[candidate]);
              }
            }
          } else if (typeof childValue === 'string') {
            pushLaw(childValue);
          }
        }
        if (REWRITE_ARRAY_KEYS.has(childKey) && Array.isArray(childValue)) {
          counts.push(childValue.length);
        }
        if (REWRITE_COUNT_KEYS.has(childKey) && typeof childValue === 'number') {
          counts.push(childValue);
        }
        stack.push({ value: childValue, key: childKey, parentKey: key });
      }
    }
  }

  return { laws, rewrites, counts };
}

function resolveRewriteCount(values) {
  let max = 0;
  for (const value of values) {
    if (typeof value !== 'number') continue;
    if (!Number.isFinite(value)) continue;
    if (value > max) max = value;
  }
  return max;
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
  return Array.from(seen).sort((a, b) => a.localeCompare(b));
}

export { buildPlan };

const invokedDirectly =
  typeof process.argv[1] === 'string' &&
  import.meta.url === pathToFileURL(resolve(process.argv[1])).href;

if (invokedDirectly) {
  main().catch((error) => {
    console.error(error instanceof Error ? error.message : String(error));
    process.exit(1);
  });
}
