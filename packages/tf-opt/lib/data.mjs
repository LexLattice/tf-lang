import { readFile } from 'node:fs/promises';
import { dirname, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';
import { listLawNames } from '../../tf-l0-proofs/src/smt-laws.mjs';

const HERE = dirname(fileURLToPath(new URL('.', import.meta.url)));
const CATALOG_CANDIDATES = [
  resolve(HERE, '..', '..', 'tf-l0-spec', 'spec', 'catalog.json'),
  fileURLToPath(new URL('../../tf-l0-spec/spec/catalog.json', import.meta.url)),
  resolve(process.cwd(), 'packages/tf-l0-spec/spec/catalog.json'),
];

const LAW_NAMES = Object.freeze(listLawNames());
const LAW_NAME_SET = new Set(LAW_NAMES);

let primitiveEffectMapPromise;

export async function readJsonFile(path, defaultValue = {}) {
  try {
    const raw = await readFile(path, 'utf8');
    return JSON.parse(raw);
  } catch (error) {
    if (error && error.code === 'ENOENT') return defaultValue;
    throw error;
  }
}

async function readCatalogStrict() {
  for (const candidate of CATALOG_CANDIDATES) {
    try {
      const raw = await readFile(candidate, 'utf8');
      const json = JSON.parse(raw);
      if (json && Array.isArray(json.primitives) && json.primitives.length > 0) {
        return json;
      }
    } catch {
      // try next
    }
  }
  throw new Error('tf-opt: unable to load tf-l0-spec/spec/catalog.json (no primitives found)');
}

/**
 * Returns a fresh Map(name -> effects[]) built from the catalog.
 * Names are lower-cased for canonical matching.
 */
export async function loadPrimitiveEffectMap() {
  const catalog = await readCatalogStrict();
  const entries = new Map();
  for (const primitive of catalog.primitives || []) {
    if (!primitive || typeof primitive !== 'object') continue;
    const name = typeof primitive.name === 'string' ? primitive.name.toLowerCase().trim() : '';
    if (!name) continue;
    const effects = Array.isArray(primitive.effects)
      ? primitive.effects.map((e) => String(e))
      : [];
    entries.set(name, effects);
  }
  if (entries.size === 0) {
    throw new Error('tf-opt: catalog parsed but produced no effect entries');
  }
  return entries;
}

export function getKnownLawNames() {
  return LAW_NAMES;
}

export function isKnownLaw(name) {
  return typeof name === 'string' && LAW_NAME_SET.has(name);
}

/* Optional helpers kept for compatibility */
export function canonicalPrimitiveName(value) {
  if (typeof value !== 'string') return '';
  return value.trim().toLowerCase();
}

export function canonicalLawName(value) {
  if (typeof value !== 'string') return '';
  return value.trim();
}
