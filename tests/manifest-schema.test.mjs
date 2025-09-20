import test from 'node:test';
import assert from 'node:assert/strict';
import { execFile } from 'node:child_process';
import { promisify } from 'node:util';
import { readFile } from 'node:fs/promises';
import { fileURLToPath } from 'node:url';
import { dirname, resolve } from 'node:path';
import Ajv2020 from 'ajv/dist/2020.js';

const execFileAsync = promisify(execFile);
const __dirname = dirname(fileURLToPath(import.meta.url));
const schemaPath = resolve(__dirname, '../schemas/manifest.v0.4.schema.json');
const schema = JSON.parse(await readFile(schemaPath, 'utf8'));
const ajv = new Ajv2020({ allErrors: true, strict: false });
const validate = ajv.compile(schema);

function assertValid(manifest) {
  const result = validate(manifest);
  assert.equal(result, true, JSON.stringify(validate.errors, null, 2));
}

function assertInvalid(manifest) {
  const result = validate(manifest);
  assert.equal(result, false, 'Expected manifest to be invalid');
}

test('publish flow manifest validates as new shape', async () => {
  const { stdout } = await execFileAsync('node', [
    'packages/tf-compose/bin/tf-manifest.mjs',
    'examples/flows/manifest_publish.tf'
  ]);
  const manifest = JSON.parse(stdout);
  assertValid(manifest);
  assert.ok(Array.isArray(manifest.required_effects));
  assert.ok(manifest.footprints_rw && Array.isArray(manifest.footprints_rw.reads));
  assert.ok(manifest.qos && manifest.qos.delivery_guarantee === 'at-least-once');
});

test('storage flow manifest validates as new shape', async () => {
  const { stdout } = await execFileAsync('node', [
    'packages/tf-compose/bin/tf-manifest.mjs',
    'examples/flows/manifest_storage.tf'
  ]);
  const manifest = JSON.parse(stdout);
  assertValid(manifest);
  assert.ok(Array.isArray(manifest.required_effects));
  assert.ok(manifest.footprints_rw && Array.isArray(manifest.footprints_rw.writes));
});

test('legacy manifest shape validates', () => {
  const legacyManifest = {
    effects: ['Network.Out'],
    footprints: [
      { uri: 'storage://bucket/object', mode: 'read' },
      { uri: 'storage://bucket/object', mode: 'write' }
    ],
    scopes: []
  };
  assertValid(legacyManifest);
});

test('missing footprint mode fails validation', () => {
  const badManifest = {
    effects: ['Network.Out'],
    footprints: [
      { uri: 'storage://bucket/object' }
    ],
    scopes: []
  };
  assertInvalid(badManifest);
});
