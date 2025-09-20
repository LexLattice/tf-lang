import test from 'node:test';
import assert from 'node:assert/strict';
import { readFile } from 'node:fs/promises';

const raw = await readFile('packages/tf-l0-spec/spec/catalog.json', 'utf8');
const catalog = JSON.parse(raw);

function findPrimitive(id) {
  return (catalog.primitives || []).find(primitive => primitive.id === id);
}

test('seed primitive effects remain curated', () => {
  const writeObject = findPrimitive('tf:resource/write-object@1');
  assert.ok(writeObject, 'write-object primitive present');
  assert.deepEqual(writeObject.effects, ['Storage.Write']);
});

test('all primitives have at least one effect tag', () => {
  const missing = (catalog.primitives || []).filter(
    primitive => !Array.isArray(primitive.effects) || primitive.effects.length === 0
  );
  assert.deepEqual(missing, [], 'primitives without effects');
});

test('network primitives include qos delivery guarantee', () => {
  const networkPrimitives = (catalog.primitives || []).filter(
    primitive =>
      Array.isArray(primitive.effects) &&
      primitive.effects.some(effect => effect.startsWith('Network.'))
  );

  assert.ok(networkPrimitives.length > 0, 'network primitives present');

  for (const primitive of networkPrimitives) {
    assert.ok(
      primitive.qos &&
        typeof primitive.qos === 'object' &&
        Object.hasOwn(primitive.qos, 'delivery_guarantee') &&
        primitive.qos.delivery_guarantee,
      `missing delivery_guarantee for ${primitive.id}`
    );
  }
});
