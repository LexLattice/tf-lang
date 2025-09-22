// @tf-test kind=infra area=manifest speed=fast deps=node

import test from 'node:test';
import assert from 'node:assert/strict';
import { readFile } from 'node:fs/promises';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { execFile } from 'node:child_process';
import { promisify } from 'node:util';
import Ajv from 'ajv/dist/2020.js';

const execFileAsync = promisify(execFile);

const __dirname = path.dirname(fileURLToPath(import.meta.url));
const repoRoot = path.resolve(__dirname, '..');
const schemaPath = path.resolve(repoRoot, 'schemas', 'manifest.v0.4.schema.json');

const schema = JSON.parse(await readFile(schemaPath, 'utf8'));
const ajv = new Ajv({ strict: true, allErrors: true });
const validate = ajv.compile(schema);

function formatErrors(errors) {
  return (errors ?? [])
    .map((error) => `${error.instancePath || '/'} ${error.message ?? ''}`.trim())
    .join('; ');
}

function assertValid(manifest, message = 'expected manifest to validate') {
  if (validate(manifest)) {
    return;
  }
  assert.fail(`${message}: ${formatErrors(validate.errors)}`);
}

function assertInvalid(manifest, message = 'expected manifest to be rejected') {
  if (!validate(manifest)) {
    assert.ok((validate.errors ?? []).length > 0, 'validation failed without errors');
    return;
  }
  assert.fail(message);
}

async function loadManifest(flowPath) {
  const { stdout } = await execFileAsync(
    'node',
    ['packages/tf-compose/bin/tf-manifest.mjs', flowPath],
    { cwd: repoRoot }
  );
  return JSON.parse(stdout);
}

test('publish flow manifest validates via new shape', async () => {
  const manifest = await loadManifest('examples/flows/manifest_publish.tf');
  assert.ok(Array.isArray(manifest.required_effects) && manifest.required_effects.length > 0);
  assert.ok(manifest.footprints_rw && 'reads' in manifest.footprints_rw);
  assert.ok(manifest.qos && manifest.qos.delivery_guarantee);
  assertValid(manifest, 'publish manifest failed schema validation');
});

test('storage flow manifest validates via new shape', async () => {
  const manifest = await loadManifest('examples/flows/manifest_storage.tf');
  assert.ok(Array.isArray(manifest.required_effects) && manifest.required_effects.length > 0);
  assertValid(manifest, 'storage manifest failed schema validation');
});

test('legacy shape with effects/footprints/scopes still validates', () => {
  const legacyManifest = {
    effects: ['Network.Out'],
    footprints: [
      {
        uri: 'res://kv/foo',
        mode: 'read'
      }
    ],
    scopes: []
  };

  assertValid(legacyManifest, 'legacy manifest rejected');
});

test('footprint entries require mode', () => {
  const badManifest = {
    required_effects: ['Network.Out'],
    footprints_rw: {
      reads: [
        {
          uri: 'res://kv/foo'
        }
      ],
      writes: []
    },
    qos: {
      delivery_guarantee: 'at-least-once',
      ordering: 'per-key'
    }
  };

  assertInvalid(badManifest, 'manifest without mode unexpectedly passed');
});

test('legacy manifest rejects required_effects mixing shapes', () => {
  const mixedManifest = {
    effects: ['Network.Out'],
    footprints: [
      {
        uri: 'res://kv/foo',
        mode: 'read'
      }
    ],
    scopes: [],
    required_effects: ['Network.Out']
  };

  assertInvalid(mixedManifest, 'legacy manifest with required_effects unexpectedly passed');
});

test('new manifest requires qos ordering', () => {
  const qosMissingOrdering = {
    required_effects: ['Network.Out'],
    footprints_rw: {
      reads: [
        {
          uri: 'res://kv/foo',
          mode: 'read'
        }
      ],
      writes: []
    },
    qos: {
      delivery_guarantee: 'exactly-once'
    }
  };

  assertInvalid(qosMissingOrdering, 'manifest without qos ordering unexpectedly passed');
});
