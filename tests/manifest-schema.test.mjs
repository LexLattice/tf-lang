import { test } from 'node:test';
import assert from 'node:assert/strict';
import { execFile } from 'node:child_process';
import { readFile } from 'node:fs/promises';
import { fileURLToPath } from 'node:url';
import path from 'node:path';
import { promisify } from 'node:util';
import Ajv2020 from 'ajv/dist/2020.js';

const execFileAsync = promisify(execFile);
const __dirname = path.dirname(fileURLToPath(import.meta.url));
const schemaPath = path.resolve(__dirname, '..', 'schemas', 'manifest.v0.4.schema.json');
const schema = JSON.parse(await readFile(schemaPath, 'utf8'));
const ajv = new Ajv2020({ allErrors: true });
const validate = ajv.compile(schema);

function ensureValid(manifest, context) {
  const valid = validate(manifest);
  if (!valid) {
    const message = (validate.errors ?? [])
      .map((error) => `${error.instancePath || '(root)'} ${error.message}`)
      .join('\n');
    assert.fail(`${context}:\n${message}`);
  }
}

function ensureInvalid(manifest, context) {
  const valid = validate(manifest);
  if (valid) {
    assert.fail(`${context}: expected validation to fail`);
  }
}

async function loadManifest(flowPath) {
  const { stdout } = await execFileAsync('node', [
    'packages/tf-compose/bin/tf-manifest.mjs',
    flowPath
  ]);
  return JSON.parse(stdout);
}

test('publish manifest validates with new fields present', async () => {
  const manifest = await loadManifest('examples/flows/manifest_publish.tf');
  assert.ok(Array.isArray(manifest.required_effects), 'required_effects missing');
  assert.ok(manifest.footprints_rw && typeof manifest.footprints_rw === 'object', 'footprints_rw missing');
  assert.ok(manifest.qos && typeof manifest.qos === 'object', 'qos missing');
  ensureValid(manifest, 'publish manifest should validate');
});

test('storage manifest validates with new fields present', async () => {
  const manifest = await loadManifest('examples/flows/manifest_storage.tf');
  assert.ok(Array.isArray(manifest.required_effects), 'required_effects missing');
  assert.ok(manifest.footprints_rw && typeof manifest.footprints_rw === 'object', 'footprints_rw missing');
  assert.ok(manifest.qos && typeof manifest.qos === 'object', 'qos missing');
  ensureValid(manifest, 'storage manifest should validate');
});

test('legacy-only manifest validates', () => {
  const legacyManifest = {
    effects: ['Network.Out'],
    footprints: [
      { uri: 'https://example.com/resource', mode: 'read' }
    ],
    scopes: []
  };
  ensureValid(legacyManifest, 'legacy manifest should validate');
});

test('footprint without mode fails validation', () => {
  const badManifest = {
    effects: ['Network.Out'],
    footprints: [
      { uri: 'https://example.com/resource' }
    ],
    scopes: []
  };
  ensureInvalid(badManifest, 'footprint without mode should fail');
});
