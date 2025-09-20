import test from 'node:test';
import assert from 'node:assert/strict';
import { readFile } from 'node:fs/promises';

async function loadCatalog() {
  const raw = await readFile('packages/tf-l0-spec/spec/catalog.json', 'utf8');
  return JSON.parse(raw);
}

test('seed effects are preserved for write-object', async () => {
  const catalog = await loadCatalog();
  const primitive = catalog.primitives.find(
    entry => entry.id === 'tf:resource/write-object@1'
  );
  assert.ok(primitive, 'write-object primitive exists');
  assert.deepEqual(primitive.effects, ['Storage.Write']);
});

test('no primitives have empty effects after derivation', async () => {
  const catalog = await loadCatalog();
  for (const primitive of catalog.primitives) {
    assert.ok(
      Array.isArray(primitive.effects) && primitive.effects.length > 0,
      `${primitive.id} should have derived effects`
    );
  }
});

test('network primitives include delivery_guarantee in qos', async () => {
  const catalog = await loadCatalog();
  for (const primitive of catalog.primitives) {
    if (
      Array.isArray(primitive.effects) &&
      primitive.effects.some(effect => effect.startsWith('Network.'))
    ) {
      assert.ok(primitive.qos, `${primitive.id} qos missing`);
      assert.ok(
        primitive.qos.delivery_guarantee,
        `${primitive.id} missing delivery_guarantee`
      );
    }
  }
});
