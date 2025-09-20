import { mkdir, readFile, writeFile } from 'node:fs/promises';
import { canonicalize } from '../packages/tf-l0-spec/scripts/canonical-json.mjs';

const catalogPath = 'packages/tf-l0-spec/spec/catalog.json';
const outputDir = 'out/0.4/spec';
const jsonOutputPath = `${outputDir}/effects-summary.json`;
const textOutputPath = `${outputDir}/effects-summary.txt`;

const raw = await readFile(catalogPath, 'utf8');
const catalog = JSON.parse(raw);

const effectCounts = {};
const unknownPrimitives = [];
let networkTotal = 0;
let networkWithDelivery = 0;
let networkWithOrdering = 0;

for (const primitive of catalog.primitives ?? []) {
  const effects = Array.isArray(primitive.effects) ? primitive.effects : [];
  if (effects.length === 0) {
    unknownPrimitives.push({ id: primitive.id, name: primitive.name });
  }

  const families = new Set();
  for (const effect of effects) {
    const family = effect.includes('.') ? effect.split('.')[0] : effect;
    families.add(family);
  }

  for (const family of families) {
    effectCounts[family] = (effectCounts[family] ?? 0) + 1;
  }

  const hasNetworkEffect = effects.some(effect => effect.startsWith('Network.'));
  if (hasNetworkEffect) {
    networkTotal += 1;
    const qos = primitive.qos;
    if (qos && typeof qos === 'object') {
      if (qos.delivery_guarantee) networkWithDelivery += 1;
      if (qos.ordering) networkWithOrdering += 1;
    }
  }
}

await mkdir(outputDir, { recursive: true });

const summary = {
  effect_counts: effectCounts,
  network_qos: {
    total: networkTotal,
    with_delivery_guarantee: networkWithDelivery,
    with_ordering: networkWithOrdering
  },
  unknown_primitives: unknownPrimitives
};

await writeFile(jsonOutputPath, canonicalize(summary) + '\n', 'utf8');

const effectTotals = Object.entries(effectCounts)
  .sort((a, b) => a[0].localeCompare(b[0]))
  .map(([family, count]) => `${family}=${count}`)
  .join(', ');
const unknownTotal = unknownPrimitives.length;
const textSummary = `Effects: ${effectTotals || 'none'}; Unknown: ${unknownTotal}; Network QoS: delivery ${networkWithDelivery}/${networkTotal}, ordering ${networkWithOrdering}/${networkTotal}`;

await writeFile(textOutputPath, `${textSummary}\n`, 'utf8');
