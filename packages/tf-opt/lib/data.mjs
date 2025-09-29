import { readFile } from 'node:fs/promises';
import { dirname, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';
import { listLawNames } from '../../tf-l0-proofs/src/smt-laws.mjs';

const HERE = dirname(fileURLToPath(import.meta.url));
const CATALOG_PATH = resolve(HERE, '..', '..', 'tf-l0-spec', 'spec', 'catalog.json');

const LAW_NAMES = Object.freeze(listLawNames());
const LAW_NAME_SET = new Set(LAW_NAMES);

let primitiveEffectMapPromise;
let catalogCachePromise;

export async function readJsonFile(path, defaultValue = {}) {
  try {
    const raw = await readFile(path, 'utf8');
    return JSON.parse(raw);
  } catch (error) {
    if (error && error.code === 'ENOENT') {
      return defaultValue;
    }
    throw error;
  }
}

async function readCatalog() {
  if (!catalogCachePromise) {
    catalogCachePromise = readJsonFile(CATALOG_PATH, {});
  }
  return catalogCachePromise;
}

export async function loadPrimitiveEffectMap() {
  if (!primitiveEffectMapPromise) {
    primitiveEffectMapPromise = (async () => {
      const catalog = await readCatalog();
      const entries = new Map();
      for (const primitive of catalog.primitives || []) {
        if (!primitive || typeof primitive !== 'object') {
          continue;
        }
        const name = typeof primitive.name === 'string' ? primitive.name.toLowerCase() : '';
        if (!name) {
          continue;
        }
        const effects = Array.isArray(primitive.effects)
          ? primitive.effects.map((effect) => String(effect))
          : [];
        entries.set(name, effects);
      }
      return entries;
    })();
  }
  const cached = await primitiveEffectMapPromise;
  return new Map(cached);
}

export function getKnownLawNames() {
  return LAW_NAMES;
}

export function isKnownLaw(name) {
  return typeof name === 'string' && LAW_NAME_SET.has(name);
}
