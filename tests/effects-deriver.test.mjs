import test from 'node:test';
import assert from 'node:assert/strict';
import { readFile } from 'node:fs/promises';

async function loadCatalog() {
  const raw = await readFile('packages/tf-l0-spec/spec/catalog.json', 'utf8');
  return JSON.parse(raw);
}

test('derive-effects: curated seed entries retain their effects', async () => {
  const catalog = await loadCatalog();
  const primitive = catalog.primitives.find(p => p.id === 'tf:resource/write-object@1');
  assert.ok(primitive, 'write-object primitive present');
  assert.deepEqual(primitive.effects, ['Storage.Write']);
});

test('derive-effects: all primitives have non-empty effects', async () => {
  const catalog = await loadCatalog();
  const missing = catalog.primitives
    .filter(p => !Array.isArray(p.effects) || p.effects.length === 0)
    .map(p => p.id);
  assert.equal(missing.length, 0, `primitives without effects: ${missing.join(', ')}`);
});

test('derive-effects: network primitives expose qos delivery guarantees', async () => {
  const catalog = await loadCatalog();
  const networkPrimitives = catalog.primitives.filter(p =>
    Array.isArray(p.effects) && p.effects.some(effect => effect.startsWith('Network.'))
  );
  assert.ok(networkPrimitives.length > 0, 'expected network primitives in catalog');
  const missing = networkPrimitives
    .filter(p => typeof p.qos?.delivery_guarantee !== 'string' || p.qos.delivery_guarantee.length === 0)
    .map(p => p.id);
  assert.equal(missing.length, 0, `network primitives missing qos.delivery_guarantee: ${missing.join(', ')}`);
});
