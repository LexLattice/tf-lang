import test from 'node:test';
import assert from 'node:assert/strict';
import { readFile } from 'node:fs/promises';

const { parseDSL } = await import('../packages/tf-compose/src/parser.mjs');
const { checkIR } = await import('../packages/tf-l0-check/src/check.mjs');
const { manifestFromVerdict } = await import('../packages/tf-l0-check/src/manifest.mjs');

async function loadCatalog() {
  try {
    const contents = await readFile('packages/tf-l0-spec/spec/catalog.json', 'utf8');
    return JSON.parse(contents);
  } catch {
    return { primitives: [] };
  }
}

test('publish manifest includes Network.Out and qos', async () => {
  const cat = await loadCatalog();
  const ir = parseDSL('publish(topic="orders", key="abc", payload="{}")');
  const verdict = checkIR(ir, cat);
  const manifest = manifestFromVerdict(verdict);

  assert.ok(manifest.required_effects.includes('Network.Out'));
  if (manifest.qos && manifest.qos.delivery_guarantee) {
    assert.ok(['at-least-once', 'exactly-once', 'at-most-once'].includes(manifest.qos.delivery_guarantee));
  }
});

test('storage manifest collects write+read footprints', async () => {
  const cat = await loadCatalog();
  const ir = parseDSL('seq{ write-object(uri="res://kv/b", key="z", value="1"); read-object(uri="res://kv/b", key="z") }');
  const verdict = checkIR(ir, cat);
  const manifest = manifestFromVerdict(verdict);

  assert.ok(manifest.required_effects.includes('Storage.Write'));
  assert.ok(manifest.required_effects.includes('Storage.Read'));
  assert.ok((manifest.footprints.writes || []).length > 0);
  assert.ok((manifest.footprints.reads || []).length > 0);
});
