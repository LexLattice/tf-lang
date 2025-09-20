import { mkdir, readFile, writeFile } from 'node:fs/promises';
import { dirname } from 'node:path';
import { canonicalize } from '../packages/tf-l0-spec/scripts/canonical-json.mjs';

const catalogPath = 'packages/tf-l0-spec/spec/catalog.json';
const outputJsonPath = 'out/0.4/spec/effects-summary.json';
const outputTextPath = 'out/0.4/spec/effects-summary.txt';

const catalog = JSON.parse(await readFile(catalogPath, 'utf8'));
const effectCounts = new Map();
const unknownEffects = [];
const networkPrimitives = [];

for (const primitive of catalog.primitives) {
  if (!Array.isArray(primitive.effects) || primitive.effects.length === 0) {
    unknownEffects.push(primitive.id);
    continue;
  }

  for (const effect of primitive.effects) {
    effectCounts.set(effect, (effectCounts.get(effect) || 0) + 1);
  }

  if (primitive.effects.some(effect => effect.startsWith('Network.')))
    networkPrimitives.push(primitive);
}

const networkMissingDelivery = networkPrimitives
  .filter(primitive => !primitive.qos || !primitive.qos.delivery_guarantee)
  .map(primitive => primitive.id)
  .sort();

const networkMissingOrdering = networkPrimitives
  .filter(primitive => !primitive.qos || !primitive.qos.ordering)
  .map(primitive => primitive.id)
  .sort();

const sortedEffectCounts = Object.fromEntries(
  Array.from(effectCounts.entries()).sort(([a], [b]) => a.localeCompare(b))
);

const summary = {
  effect_counts: sortedEffectCounts,
  network_qos: {
    missing_delivery_guarantee: networkMissingDelivery,
    missing_ordering: networkMissingOrdering,
    total: networkPrimitives.length,
    with_delivery_guarantee:
      networkPrimitives.length - networkMissingDelivery.length,
    with_ordering: networkPrimitives.length - networkMissingOrdering.length
  },
  unknown_effects: unknownEffects.sort()
};

await mkdir(dirname(outputJsonPath), { recursive: true });
await writeFile(outputJsonPath, canonicalize(summary) + '\n', 'utf8');

const totalPrimitives = catalog.primitives.length;
const effectParts = Object.entries(sortedEffectCounts)
  .map(([effect, count]) => `${effect}=${count}`)
  .join(', ');

const textLine = [
  `Total primitives: ${totalPrimitives}`,
  `Effects: ${effectParts || 'none'}`,
  `Network QoS: delivery_guarantee ${
    summary.network_qos.with_delivery_guarantee
  }/${summary.network_qos.total}, ordering ${
    summary.network_qos.with_ordering
  }/${summary.network_qos.total}`,
  `Unknown effects: ${summary.unknown_effects.length}`
].join('; ');

await writeFile(outputTextPath, `${textLine}\n`, 'utf8');
