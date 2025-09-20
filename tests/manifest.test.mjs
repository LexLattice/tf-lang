import test from 'node:test';
import assert from 'node:assert/strict';
import { readFile } from 'node:fs/promises';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { spawn } from 'node:child_process';

const { parseDSL } = await import('../packages/tf-compose/src/parser.mjs');
const { checkIR } = await import('../packages/tf-l0-check/src/check.mjs');
const { manifestFromVerdict } = await import('../packages/tf-l0-check/src/manifest.mjs');

const __dirname = path.dirname(fileURLToPath(import.meta.url));
const catalogPath = path.resolve(
  __dirname,
  '..',
  'packages/tf-l0-spec/spec/catalog.json'
);

async function loadCatalog() {
  const contents = await readFile(catalogPath, 'utf8');
  return JSON.parse(contents);
}

test('publish manifest includes Network.Out and qos', async () => {
  const cat = await loadCatalog();
  const ir = parseDSL('publish(topic="orders", key="abc", payload="{}")');
  const verdict = checkIR(ir, cat);
  const manifest = manifestFromVerdict(verdict);

  assert.ok(manifest.required_effects.includes('Network.Out'));
  assert.ok(manifest.qos && manifest.qos.delivery_guarantee);
});

test('storage manifest collects write+read footprints', async () => {
  const cat = await loadCatalog();
  const ir = parseDSL('seq{ write-object(uri="res://kv/b", key="z", value="1"); read-object(uri="res://kv/b", key="z") }');
  const verdict = checkIR(ir, cat);
  const manifest = manifestFromVerdict(verdict);

  assert.ok(manifest.required_effects.includes('Storage.Write'));
  assert.ok(manifest.required_effects.includes('Storage.Read'));
  assert.ok((manifest.footprints_rw.writes || []).length > 0);
  assert.ok((manifest.footprints_rw.reads || []).length > 0);
  assert.strictEqual(
    manifest.footprints.length,
    (manifest.footprints_rw.reads || []).length +
      (manifest.footprints_rw.writes || []).length
  );
});

test('CLI reports missing flow file with non-zero exit', async () => {
  const cli = spawn('node', ['packages/tf-compose/bin/tf-manifest.mjs', 'nope.tf'], {
    cwd: path.resolve(__dirname, '..'),
    stdio: ['ignore', 'pipe', 'pipe']
  });

  const stderrChunks = [];
  cli.stderr.on('data', (chunk) => stderrChunks.push(chunk));

  const exitCode = await new Promise((resolve) => {
    cli.on('close', resolve);
  });

  assert.notStrictEqual(exitCode, 0);
  const stderr = Buffer.concat(stderrChunks).toString('utf8');
  assert.match(stderr, /Failed to read flow/);
});
