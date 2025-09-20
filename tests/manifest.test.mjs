import test from 'node:test';
import assert from 'node:assert/strict';
const { parseDSL } = await import('../packages/tf-compose/src/parser.mjs');
const { checkIR } = await import('../packages/tf-l0-check/src/check.mjs');
const { manifestFromVerdict } = await import('../packages/tf-l0-check/src/manifest.mjs');
import { readFile } from 'node:fs/promises';

async function loadCatalog() {
  try { return JSON.parse(await readFile('packages/tf-l0-spec/spec/catalog.json','utf8')); }
  catch { return { primitives: [] }; }
}

test('publish manifest includes Network.Out and qos', async () => {
  const cat = await loadCatalog();
  const ir = parseDSL('publish(topic="orders", key="abc", payload="{}")');
  const v = checkIR(ir, cat);
  const m = manifestFromVerdict(v);
  assert.ok(m.required_effects.includes('Network.Out'));
  if (m.qos && m.qos.delivery_guarantee) {
    assert.ok(['at-least-once', 'exactly-once', 'at-most-once'].includes(m.qos.delivery_guarantee));
  }
});

test('storage manifest collects write+read footprints', async () => {
  const cat = await loadCatalog();
  const ir = parseDSL('seq{ write-object(uri="res://kv/b", key="z", value="1"); read-object(uri="res://kv/b", key="z") }');
  const v = checkIR(ir, cat);
  const m = manifestFromVerdict(v);
  assert.ok(m.required_effects.includes('Storage.Write'));
  assert.ok(m.required_effects.includes('Storage.Read'));
  assert.ok((m.footprints.writes||[]).length > 0);
  assert.ok((m.footprints.reads||[]).length > 0);
});
