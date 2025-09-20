import { readFile, writeFile } from 'node:fs/promises';
import { join } from 'node:path';
import { canonicalize } from './canonical-json.mjs';

const spec = 'packages/tf-l0-spec/spec';

const effectMap = new Map([
  ['acknowledge', ['Network.Out']],
  ['compare-and-swap', ['Storage.Write']],
  ['decrypt', ['Crypto']],
  ['delete-object', ['Storage.Write']],
  ['deserialize', ['Pure']],
  ['emit-log', ['Observability']],
  ['emit-metric', ['Observability']],
  ['encrypt', ['Crypto']],
  ['hash', ['Pure']],
  ['list-objects', ['Storage.Read']],
  ['publish', ['Network.Out']],
  ['read-object', ['Storage.Read']],
  ['request', ['Network.Out']],
  ['serialize', ['Pure']],
  ['sign-data', ['Crypto']],
  ['subscribe', ['Network.In']],
  ['verify-signature', ['Crypto']],
  ['write-object', ['Storage.Write']]
]);

function deriveEffects(name) {
  const n = (name || '').toLowerCase();
  return effectMap.get(n) || [];
}

const catalog = JSON.parse(await readFile(join(spec, 'catalog.json'), 'utf8'));
for (const primitive of catalog.primitives) {
  if (!Array.isArray(primitive.effects) || primitive.effects.length === 0) {
    const derived = deriveEffects(primitive.name);
    if (derived.length === 0) {
      console.warn(`No derived effects for primitive ${primitive.id}`);
    }
    primitive.effects = derived;
  }

  if (
    Array.isArray(primitive.effects) &&
    primitive.effects.some(effect => effect.startsWith('Network.'))
  ) {
    if (!primitive.qos || Object.keys(primitive.qos).length === 0) {
      primitive.qos = {
        delivery_guarantee: 'at-least-once',
        ordering: 'per-key'
      };
    }
  }
}

await writeFile(
  join(spec, 'effects.json'),
  canonicalize({
    catalog_semver: catalog.catalog_semver,
    effects: catalog.primitives.map(primitive => ({
      id: primitive.id,
      effects: primitive.effects
    }))
  }) + '\n',
  'utf8'
);

await writeFile(join(spec, 'catalog.json'), canonicalize(catalog) + '\n', 'utf8');
console.log('effects derived and catalog.json updated.');
