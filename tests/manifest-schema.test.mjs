import test from 'node:test';
import assert from 'node:assert/strict';
import { readFile } from 'node:fs/promises';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { spawn } from 'node:child_process';
import Ajv from 'ajv/dist/2020.js';

const __dirname = path.dirname(fileURLToPath(import.meta.url));
const repoRoot = path.resolve(__dirname, '..');
const schemaPath = fileURLToPath(new URL('../schemas/manifest.v0.4.schema.json', import.meta.url));
const schema = JSON.parse(await readFile(schemaPath, 'utf8'));
const ajv = new Ajv({ strict: true, allErrors: true });
const validate = ajv.compile(schema);

async function readManifestFromCli(flowPath) {
  const cli = spawn('node', ['packages/tf-compose/bin/tf-manifest.mjs', flowPath], {
    cwd: repoRoot,
    stdio: ['ignore', 'pipe', 'inherit']
  });

  const stdoutChunks = [];
  cli.stdout.on('data', (chunk) => stdoutChunks.push(chunk));

  const exitCode = await new Promise((resolve, reject) => {
    cli.on('error', reject);
    cli.on('close', resolve);
  });

  assert.strictEqual(exitCode, 0, 'manifest CLI exited with non-zero status');
  const json = Buffer.concat(stdoutChunks).toString('utf8');
  return JSON.parse(json);
}

test('publish flow manifest validates against v0.4 schema', async () => {
  const manifest = await readManifestFromCli('examples/flows/manifest_publish.tf');
  const ok = validate(manifest);
  if (!ok) {
    assert.fail(`publish manifest failed schema validation:\n${ajv.errorsText(validate.errors, { separator: '\n' })}`);
  }

  assert.ok(Array.isArray(manifest.required_effects));
  assert.ok(manifest.footprints_rw);
  assert.ok(manifest.qos);
});

test('storage flow manifest validates against v0.4 schema', async () => {
  const manifest = await readManifestFromCli('examples/flows/manifest_storage.tf');
  const ok = validate(manifest);
  if (!ok) {
    assert.fail(`storage manifest failed schema validation:\n${ajv.errorsText(validate.errors, { separator: '\n' })}`);
  }

  assert.ok(Array.isArray(manifest.required_effects));
  assert.ok(manifest.footprints_rw);
  assert.ok(manifest.qos);
});

test('legacy manifest shape still validates', () => {
  const legacyManifest = {
    effects: ['Network.Out'],
    scopes: [],
    footprints: [
      {
        uri: 'res://kv/orders',
        mode: 'read'
      }
    ]
  };

  const ok = validate(legacyManifest);
  if (!ok) {
    assert.fail(`legacy manifest failed schema validation:\n${ajv.errorsText(validate.errors, { separator: '\n' })}`);
  }
});

test('footprint without mode is rejected', () => {
  const badManifest = {
    required_effects: ['Network.Out'],
    footprints_rw: {
      reads: [
        {
          uri: 'res://kv/orders'
        }
      ],
      writes: []
    },
    qos: {
      delivery_guarantee: 'at-least-once',
      ordering: 'per-key'
    }
  };

  const ok = validate(badManifest);
  assert.strictEqual(ok, false, 'manifest missing footprint mode should be invalid');
});
