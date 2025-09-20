import { readFile, writeFile } from 'node:fs/promises';
import { join } from 'node:path';
import { canonicalize } from './canonical-json.mjs';

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

const NETWORK_QOS_DEFAULT = {
  delivery_guarantee: 'at-least-once',
  ordering: 'per-key'
};

const catalogPath = join(spec, 'catalog.json');
const catalog = JSON.parse(await readFile(catalogPath, 'utf8'));

for (const primitive of catalog.primitives) {
  if (!Array.isArray(primitive.effects) || primitive.effects.length === 0) {
    const derived = EFFECT_RULES.get(primitive.name.toLowerCase()) ?? [];
    primitive.effects = derived;
  }

  const hasNetworkEffect = Array.isArray(primitive.effects) && primitive.effects.some(effect => effect.startsWith('Network.'));
  if (hasNetworkEffect && primitive.qos == null) {
    primitive.qos = { ...NETWORK_QOS_DEFAULT };
  }
}

await writeFile(join(spec, 'effects.json'), canonicalize({
  catalog_semver: catalog.catalog_semver,
  effects: catalog.primitives.map(primitive => ({
    id: primitive.id,
    effects: primitive.effects
  }))
}) + '\n', 'utf8');

await writeFile(catalogPath, canonicalize(catalog) + '\n', 'utf8');

console.log('effects derived and catalog.json updated.');
