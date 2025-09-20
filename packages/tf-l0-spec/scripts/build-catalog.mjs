/**
 * A1: unify YAML catalogs into a normalized catalog.json.
 * For hard-grounding, we load ids.json and project each primitive into the catalog
 * with placeholders for effects/footprints/data_classes/errors to be filled in later.
 */
import { readFile, writeFile, readdir } from 'node:fs/promises';
import { join } from 'node:path';
import { canonicalize } from './canonical-json.mjs';

const spec = 'packages/tf-l0-spec/spec';

const ids = JSON.parse(await readFile(join(spec, 'ids.json'), 'utf8'));

async function loadSeedPrimitives() {
  const seedDir = join(spec, 'seed');
  try {
    const files = await readdir(seedDir);
    const out = [];
    for (const file of files) {
      if (!file.endsWith('.json')) continue;
      const raw = await readFile(join(seedDir, file), 'utf8');
      const parsed = JSON.parse(raw);
      const prims = Array.isArray(parsed.primitives) ? parsed.primitives : [];
      out.push(...prims);
    }
    return out;
  } catch {
    return [];
  }
}

const seedPrimitives = await loadSeedPrimitives();
const basePrimitives = ids.primitives.map(p => ({
  ...p,
  effects: [],
  reads: [],
  writes: [],
  keys: [],
  data_classes: [],
  errors: { retryable: false, categories: [] },
  qos: {}
}));

const byId = new Map(basePrimitives.map(p => [p.id, p]));
for (const seed of seedPrimitives) {
  if (!seed?.id) continue;
  const existing = byId.get(seed.id);
  if (!existing) {
    byId.set(seed.id, {
      keys: [],
      errors: { retryable: false, categories: [] },
      qos: {},
      reads: [],
      writes: [],
      data_classes: [],
      effects: [],
      ...seed
    });
    continue;
  }

  const merged = {
    ...existing,
    ...seed
  };

  const prefer = (seedVal, fallback) =>
    Array.isArray(seedVal) && seedVal.length ? seedVal : fallback;

  merged.effects = prefer(seed.effects, existing.effects || []);
  merged.reads = prefer(seed.reads, existing.reads || []);
  merged.writes = prefer(seed.writes, existing.writes || []);
  merged.data_classes = prefer(seed.data_classes, existing.data_classes || []);
  merged.qos = seed.qos || existing.qos || {};
  merged.errors = existing.errors || { retryable: false, categories: [] };
  merged.keys = existing.keys || [];

  byId.set(seed.id, merged);
}

const catalog = {
  catalog_semver: ids.catalog_semver || "0.4.0-alpha.0",
  primitives: Array.from(byId.values()).sort((a, b) => (a.id || '').localeCompare(b.id || ''))
};

await writeFile(join(spec, 'catalog.json'), canonicalize(catalog) + '\n', 'utf8');
console.log("catalog.json written with", catalog.primitives.length, "primitives (seed union applied).");
