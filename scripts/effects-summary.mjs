import { readFile, writeFile, mkdir } from 'node:fs/promises';
import { canonicalize } from '../packages/tf-l0-spec/scripts/canonical-json.mjs';

const catalogPath = 'packages/tf-l0-spec/spec/catalog.json';
const outputDir = 'out/0.4/spec';
const summaryJsonPath = `${outputDir}/effects-summary.json`;
const summaryTextPath = `${outputDir}/effects-summary.txt`;

const NETWORK_EFFECTS = new Set(['Network.In', 'Network.Out']);

const rawCatalog = await readFile(catalogPath, 'utf8');
const catalog = JSON.parse(rawCatalog);

const effectCounts = new Map();
const unknownEffects = [];
let networkTotal = 0;
let networkWithDelivery = 0;
let networkWithOrdering = 0;
const networkMissing = [];

for (const primitive of catalog.primitives) {
  const effects = Array.isArray(primitive.effects) ? primitive.effects : [];

  if (effects.length === 0) {
    unknownEffects.push(primitive.id);
  }

  for (const effect of effects) {
    effectCounts.set(effect, (effectCounts.get(effect) ?? 0) + 1);
  }

  if (effects.some(effect => NETWORK_EFFECTS.has(effect))) {
    networkTotal += 1;
    const hasDelivery =
      typeof primitive.qos?.delivery_guarantee === 'string' &&
      primitive.qos.delivery_guarantee.length > 0;
    const hasOrdering =
      typeof primitive.qos?.ordering === 'string' && primitive.qos.ordering.length > 0;

    if (hasDelivery) networkWithDelivery += 1;
    if (hasOrdering) networkWithOrdering += 1;

    if (!hasDelivery || !hasOrdering) {
      const missing = [];
      if (!hasDelivery) missing.push('delivery_guarantee');
      if (!hasOrdering) missing.push('ordering');
      networkMissing.push({ id: primitive.id, missing });
    }
  }
}

const summary = {
  catalog_semver: catalog.catalog_semver,
  effect_counts: Object.fromEntries(Array.from(effectCounts.entries()).sort(([a], [b]) => a.localeCompare(b))),
  unknown_effects: unknownEffects,
  network_qos: {
    total: networkTotal,
    with_delivery_guarantee: networkWithDelivery,
    with_ordering: networkWithOrdering,
    missing: networkMissing
  }
};

await mkdir(outputDir, { recursive: true });
await writeFile(summaryJsonPath, canonicalize(summary) + '\n', 'utf8');

const effectParts = Array.from(effectCounts.entries())
  .sort(([a], [b]) => a.localeCompare(b))
  .map(([effect, count]) => `${effect}=${count}`);
const textSummary = [
  `Effects: ${effectParts.join(', ')}`,
  `Unknown=${unknownEffects.length}`,
  `Network QoS: delivery=${networkWithDelivery}/${networkTotal}, ordering=${networkWithOrdering}/${networkTotal}`
].join(' | ');

await writeFile(summaryTextPath, `${textSummary}\n`, 'utf8');

console.log(`effects summary written to ${summaryJsonPath} and ${summaryTextPath}`);
