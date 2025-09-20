import { readFile, writeFile } from 'node:fs/promises';
import { join } from 'node:path';
import { pathToFileURL } from 'node:url';
import { canonicalize } from './canonical-json.mjs';

// NOTE: legacy regex rules replaced by EFFECT_RULES; seed overlay remains authoritative.

const spec = 'packages/tf-l0-spec/spec';

const EFFECT_RULES = new Map([
  ['read-object', ['Storage.Read']],
  ['list-objects', ['Storage.Read']],
  ['write-object', ['Storage.Write']],
  ['delete-object', ['Storage.Write']],
  ['compare-and-swap', ['Storage.Write']],
  ['publish', ['Network.Out']],
  ['request', ['Network.Out']],
  ['acknowledge', ['Network.Out']],
  ['subscribe', ['Network.In']],
  ['hash', ['Pure']],
  ['serialize', ['Pure']],
  ['deserialize', ['Pure']],
  ['sign-data', ['Crypto']],
  ['verify-signature', ['Crypto']],
  ['encrypt', ['Crypto']],
  ['decrypt', ['Crypto']],
  ['emit-metric', ['Observability']],
  ['emit-log', ['Observability']]
]);

const NETWORK_EFFECTS = new Set(['Network.In', 'Network.Out']);
const DEFAULT_NETWORK_QOS = Object.freeze({
  delivery_guarantee: 'at-least-once',
  ordering: 'per-key'
});

export function deriveEffectsFromName(name) {
  const key = typeof name === 'string' ? name.toLowerCase() : '';
  const derived = EFFECT_RULES.get(key);
  return Array.isArray(derived) ? [...derived].sort() : [];
}

export function applyEffectsAndQos(primitive) {
  if (!primitive || typeof primitive !== 'object') {
    return primitive;
  }

  const effects = primitive.effects;
  if (!effects || effects.length === 0) {
    const derived = deriveEffectsFromName(primitive.name);
    primitive.effects = derived;
  } else if (Array.isArray(effects)) {
    primitive.effects = [...effects];
    primitive.effects.sort();
  }

  const hasNetworkEffect = Array.isArray(primitive.effects)
    ? primitive.effects.some(effect => NETWORK_EFFECTS.has(effect))
    : false;

  if (hasNetworkEffect) {
    const qos = primitive.qos ?? {};
    const nextQos = { ...qos };
    let changed = primitive.qos === undefined;

    if (nextQos.delivery_guarantee === undefined) {
      nextQos.delivery_guarantee = DEFAULT_NETWORK_QOS.delivery_guarantee;
      changed = true;
    }

    if (nextQos.ordering === undefined) {
      nextQos.ordering = DEFAULT_NETWORK_QOS.ordering;
      changed = true;
    }

    if (changed) {
      primitive.qos = nextQos;
    }
  }

  return primitive;
}

export async function run() {
  const catalogPath = join(spec, 'catalog.json');
  const catalog = JSON.parse(await readFile(catalogPath, 'utf8'));

  for (const primitive of catalog.primitives) {
    applyEffectsAndQos(primitive);
  }

  const effectsEntries = catalog.primitives.map(primitive => ({
    id: primitive.id,
    effects: Array.isArray(primitive.effects) ? [...primitive.effects].sort() : []
  }));

  await writeFile(
    join(spec, 'effects.json'),
    canonicalize({
      catalog_semver: catalog.catalog_semver,
      effects: effectsEntries
    }) + '\n',
    'utf8'
  );

  await writeFile(catalogPath, canonicalize(catalog) + '\n', 'utf8');
  console.log('effects derived and catalog.json updated.');
}

const entryHref = process.argv[1] ? pathToFileURL(process.argv[1]).href : undefined;
if (import.meta.url === entryHref) {
  await run();
}
