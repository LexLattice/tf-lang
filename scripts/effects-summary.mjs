import { mkdir, readFile, writeFile } from 'node:fs/promises';
import { dirname } from 'node:path';
import { canonicalize } from '../packages/tf-l0-spec/scripts/canonical-json.mjs';

const catalogPath = 'packages/tf-l0-spec/spec/catalog.json';
const outputJsonPath = 'out/0.4/spec/effects-summary.json';
const outputTextPath = 'out/0.4/spec/effects-summary.txt';

const catalog = JSON.parse(await readFile(catalogPath, 'utf8'));

const effectCounts = new Map();
const unknownEffects = [];
const networkStats = {
  missing_qos: [],
  total: 0,
  with_delivery_guarantee: 0,
  with_ordering: 0
};

for (const primitive of catalog.primitives) {
  const effects = Array.isArray(primitive.effects) ? primitive.effects : [];
  if (effects.length === 0) {
    unknownEffects.push(primitive.id);
  }

  for (const effect of effects) {
    const family = effect.includes('.') ? effect.split('.')[0] : effect;
    effectCounts.set(family, (effectCounts.get(family) ?? 0) + 1);
  }

  const hasNetworkEffect = effects.some(effect => effect.startsWith('Network.'));
  if (hasNetworkEffect) {
    networkStats.total += 1;
    if (primitive.qos == null) {
      networkStats.missing_qos.push(primitive.id);
    } else {
      if (primitive.qos.delivery_guarantee != null) {
        networkStats.with_delivery_guarantee += 1;
      }
      if (primitive.qos.ordering != null) {
        networkStats.with_ordering += 1;
      }
      if (primitive.qos.delivery_guarantee == null || primitive.qos.ordering == null) {
        networkStats.missing_qos.push(primitive.id);
      }
    }
  }
}

const effectCountsObject = Object.fromEntries([...effectCounts.entries()].sort(([a], [b]) => a.localeCompare(b)));

const summary = {
  effect_counts: effectCountsObject,
  network_qos: {
    missing_qos: networkStats.missing_qos,
    total: networkStats.total,
    with_delivery_guarantee: networkStats.with_delivery_guarantee,
    with_ordering: networkStats.with_ordering
  },
  unknown_effects: unknownEffects
};

await mkdir(dirname(outputJsonPath), { recursive: true });
await writeFile(outputJsonPath, canonicalize(summary) + '\n', 'utf8');

const familyTotals = Object.entries(effectCountsObject)
  .map(([family, count]) => `${family}: ${count}`)
  .join(', ');
const textSummary = `Effect totals - ${familyTotals || 'none'} | Unknown: ${unknownEffects.length} | Network QoS missing: ${networkStats.missing_qos.length}/${networkStats.total}`;
await writeFile(outputTextPath, `${textSummary}\n`, 'utf8');

console.log('effects summary written.');
