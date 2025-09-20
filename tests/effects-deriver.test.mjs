import test from 'node:test';
import assert from 'node:assert/strict';
import { readFile } from 'node:fs/promises';

await import('../packages/tf-l0-spec/scripts/derive-effects.mjs');

async function loadCatalog() {
  const raw = await readFile('packages/tf-l0-spec/spec/catalog.json', 'utf8');
  return JSON.parse(raw);
}

test('seed primitive retains curated effects', async () => {
  const catalog = await loadCatalog();
  const primitive = catalog.primitives.find(p => p.id === 'tf:resource/write-object@1');
  assert.ok(primitive, 'tf:resource/write-object@1 present');
  assert.deepEqual(primitive.effects, ['Storage.Write']);
});

test('all primitives have at least one effect', async () => {
  const catalog = await loadCatalog();
  const missing = catalog.primitives.filter(
    p => !Array.isArray(p.effects) || p.effects.length === 0
  );
  assert.deepEqual(missing, [], 'no primitives missing effects');
});

test('network primitives include qos delivery guarantee', async () => {
  const catalog = await loadCatalog();
  const offending = catalog.primitives.filter(primitive => {
    if (!Array.isArray(primitive.effects)) {
      return false;
    }
    const hasNetwork = primitive.effects.some(effect => effect.startsWith('Network.'));
    if (!hasNetwork) {
      return false;
    }
    return primitive.qos == null || primitive.qos.delivery_guarantee == null;
  });
  assert.deepEqual(offending, [], 'all network primitives have qos.delivery_guarantee');
});
