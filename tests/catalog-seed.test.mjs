// @tf-test kind=product area=catalog speed=fast deps=node

import test from 'node:test';
import assert from 'node:assert/strict';
import { readFile } from 'node:fs/promises';

test('seed: write-object has writes footprint', async () => {
  const raw = await readFile('packages/tf-l0-spec/spec/catalog.json', 'utf8');
  const catalog = JSON.parse(raw);
  const primitive = (catalog.primitives || []).find(
    p => p.id === 'tf:resource/write-object@1'
  );
  assert.ok(primitive, 'write-object present in catalog');
  assert.ok(
    Array.isArray(primitive.writes) && primitive.writes.length > 0,
    'writes footprint present'
  );
});
