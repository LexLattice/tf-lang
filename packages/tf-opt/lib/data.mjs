import { readFile } from 'node:fs/promises';
import { resolve } from 'node:path';
import { fileURLToPath } from 'node:url';

const here = fileURLToPath(new URL('.', import.meta.url));
const repoRoot = resolve(here, '..', '..', '..');
const catalogPath = resolve(repoRoot, 'packages/tf-l0-spec/spec/catalog.json');
const smtModulePath = new URL('../../tf-l0-proofs/src/smt-laws.mjs', import.meta.url);

let lawAliasCache = null;
let effectMapCache = null;

export async function loadLawAliasSet() {
  if (!lawAliasCache) {
    const mod = await import(smtModulePath);
    const names = mod.listLawNames ? mod.listLawNames() : [];
    lawAliasCache = new Set(names.map((name) => canonicalLawName(name)).filter((name) => name.length > 0));
  }
  return lawAliasCache;
}

export async function loadPrimitiveEffectMap() {
  if (!effectMapCache) {
    const raw = await readFile(catalogPath, 'utf8');
    const catalog = JSON.parse(raw);
    const map = new Map();
    for (const entry of Array.isArray(catalog.primitives) ? catalog.primitives : []) {
      if (!entry || typeof entry.name !== 'string') continue;
      const name = entry.name.trim().toLowerCase();
      if (!name) continue;
      const effect = Array.isArray(entry.effects) && entry.effects.length > 0 ? entry.effects[0] : null;
      map.set(name, {
        id: entry.id ?? null,
        effect,
        domain: entry.domain ?? null,
        codomain: entry.codomain ?? null,
      });
    }
    effectMapCache = map;
  }
  return effectMapCache;
}

export function canonicalPrimitiveName(value) {
  if (typeof value !== 'string') return '';
  return value.trim().toLowerCase();
}

export function canonicalLawName(value) {
  if (typeof value !== 'string') return '';
  return value.trim();
}
