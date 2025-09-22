// @tf-test kind=product area=checker speed=fast deps=node
import test from 'node:test';
import assert from 'node:assert/strict';
import { readFile } from 'node:fs/promises';
import { applyEffectsAndQos, run as deriveEffects } from '../packages/tf-l0-spec/scripts/derive-effects.mjs';

const catalogPath = 'packages/tf-l0-spec/spec/catalog.json';

async function loadCatalog() {
  const raw = await readFile(catalogPath, 'utf8');
  return JSON.parse(raw);
}

await deriveEffects();

test('derive-effects: curated seed entries retain their effects and qos', async () => {
  const catalog = await loadCatalog();

  const writeObject = catalog.primitives.find(p => p.id === 'tf:resource/write-object@1');
  assert.ok(writeObject, 'write-object primitive present');
  assert.deepEqual(writeObject.effects, ['Storage.Write']);
  assert.deepEqual(writeObject.qos, {});

  const publish = catalog.primitives.find(p => p.id === 'tf:network/publish@1');
  assert.ok(publish, 'publish primitive present');
  assert.deepEqual(publish.effects, ['Network.Out']);
  assert.deepEqual(publish.qos, {
    delivery_guarantee: 'at-least-once',
    ordering: 'per-key'
  });
});

test('derive-effects: all primitives have non-empty effects', async () => {
  const catalog = await loadCatalog();
  const missing = catalog.primitives
    .filter(p => !Array.isArray(p.effects) || p.effects.length === 0)
    .map(p => p.id);
  assert.equal(missing.length, 0, `primitives without effects: ${missing.join(', ')}`);
});

test('derive-effects: network qos defaults fill gaps without overriding', () => {
  const seeded = applyEffectsAndQos({
    id: 'test:network/publish@1',
    name: 'publish',
    effects: ['Network.Out']
  });
  assert.deepEqual(seeded.qos, {
    delivery_guarantee: 'at-least-once',
    ordering: 'per-key'
  });

  const partial = applyEffectsAndQos({
    id: 'test:network/subscribe@1',
    name: 'subscribe',
    effects: ['Network.In'],
    qos: { delivery_guarantee: 'exactly-once' }
  });
  assert.deepEqual(partial.qos, {
    delivery_guarantee: 'exactly-once',
    ordering: 'per-key'
  });

  const curated = applyEffectsAndQos({
    id: 'test:network/request@1',
    name: 'request',
    effects: ['Network.Out'],
    qos: {
      delivery_guarantee: 'exactly-once',
      ordering: 'global'
    }
  });
  assert.deepEqual(curated.qos, {
    delivery_guarantee: 'exactly-once',
    ordering: 'global'
  });
});
