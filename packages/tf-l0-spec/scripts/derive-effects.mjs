import { readFile, writeFile } from 'node:fs/promises';
import { join } from 'node:path';
import { canonicalize } from './canonical-json.mjs';

const spec = 'packages/tf-l0-spec/spec';

const effectRules = new Map([
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

const defaultNetworkQos = {
  delivery_guarantee: 'at-least-once',
  ordering: 'per-key'
};

function deriveEffects(name = '') {
  const key = String(name).toLowerCase();
  return effectRules.get(key) ?? [];
}

const catalog = JSON.parse(await readFile(join(spec, 'catalog.json'), 'utf8'));

for (const primitive of catalog.primitives ?? []) {
  if (!Array.isArray(primitive.effects) || primitive.effects.length === 0) {
    primitive.effects = deriveEffects(primitive.name);
  }

  if (
    Array.isArray(primitive.effects) &&
    primitive.effects.some(effect => effect.startsWith('Network.'))
  ) {
    const qos = primitive.qos;
    const hasQos =
      qos && typeof qos === 'object' && Object.keys(qos).length > 0;
    if (!hasQos) {
      primitive.qos = { ...defaultNetworkQos };
    }
  }
}

await writeFile(
  join(spec, 'effects.json'),
  canonicalize({
    catalog_semver: catalog.catalog_semver,
    effects: catalog.primitives.map(primitive => ({
      effects: primitive.effects,
      id: primitive.id
    }))
  }) + '\n',
  'utf8'
);

await writeFile(
  join(spec, 'catalog.json'),
  canonicalize(catalog) + '\n',
  'utf8'
);

console.log('effects derived and catalog.json updated.');
