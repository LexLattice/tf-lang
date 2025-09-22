#!/usr/bin/env node
// scripts/audit/check-catalog.mjs
import { readFile } from 'node:fs/promises';
import path from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';

import { CANONICAL_EFFECT_FAMILIES, normalizeFamily } from '../../packages/tf-l0-check/src/effect-lattice.mjs';

const __dirname = path.dirname(fileURLToPath(import.meta.url));
const ROOT = path.resolve(__dirname, '../..');

async function loadJson(relPath) {
  const absPath = path.join(ROOT, relPath);
  try {
    const raw = await readFile(absPath, 'utf8');
    return JSON.parse(raw);
  } catch (err) {
    if (err && err.code === 'ENOENT') {
      return null;
    }
    throw err;
  }
}

function effectRecognized(effect) {
  if (typeof effect !== 'string') return false;
  const trimmed = effect.trim();
  if (trimmed.length === 0) return false;
  const normalized = normalizeFamily(trimmed);
  if (!CANONICAL_EFFECT_FAMILIES.includes(normalized)) {
    return false;
  }
  if (normalized === 'Pure' && trimmed.toLowerCase() !== 'pure') {
    return false;
  }
  return true;
}

export async function run() {
  const catalog = (await loadJson('packages/tf-l0-spec/spec/catalog.json')) || {};
  const laws = (await loadJson('packages/tf-l0-spec/spec/laws.json')) || {};

  const primitives = Array.isArray(catalog.primitives) ? catalog.primitives : [];
  const primitiveMap = new Map();
  for (const primitive of primitives) {
    if (primitive && typeof primitive === 'object' && typeof primitive.id === 'string') {
      primitiveMap.set(primitive.id, primitive);
    }
  }

  const primsMissingEffects = [];
  const effectsUnrecognized = [];

  for (const primitive of primitives) {
    if (!primitive || typeof primitive !== 'object') continue;
    const id = typeof primitive.id === 'string' ? primitive.id : '(unknown)';
    const effects = Array.isArray(primitive.effects) ? primitive.effects : [];
    if (effects.length === 0) {
      primsMissingEffects.push(id);
      continue;
    }
    for (const effect of effects) {
      if (!effectRecognized(effect)) {
        effectsUnrecognized.push(`${id}:${String(effect)}`);
      }
    }
  }

  const lawsList = Array.isArray(laws.laws) ? laws.laws : [];
  const lawsRefMissingPrims = [];
  for (const law of lawsList) {
    if (!law || typeof law !== 'object') continue;
    const appliesTo = Array.isArray(law.applies_to) ? law.applies_to : [];
    const lawId = typeof law.id === 'string' ? law.id : 'law:unknown';
    for (const entry of appliesTo) {
      if (typeof entry !== 'string') continue;
      if (!entry.startsWith('tf:')) continue;
      if (!primitiveMap.has(entry)) {
        lawsRefMissingPrims.push(`${lawId} -> ${entry}`);
      }
    }
  }

  effectsUnrecognized.sort();
  primsMissingEffects.sort();
  lawsRefMissingPrims.sort();

  const ok =
    effectsUnrecognized.length === 0 &&
    primsMissingEffects.length === 0 &&
    lawsRefMissingPrims.length === 0;

  return {
    ok,
    effects_unrecognized: effectsUnrecognized,
    prims_missing_effects: primsMissingEffects,
    laws_ref_missing_prims: lawsRefMissingPrims
  };
}

async function main() {
  const result = await run();
  process.stdout.write(`${JSON.stringify(result, null, 2)}\n`);
}

const isCli = process.argv[1]
  ? pathToFileURL(process.argv[1]).href === import.meta.url
  : false;

if (isCli) {
  main().catch((err) => {
    process.stderr.write(`audit:check-catalog failed: ${err?.stack || err}\n`);
    process.exitCode = 1;
  });
}
