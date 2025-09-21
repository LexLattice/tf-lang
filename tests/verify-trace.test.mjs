import { test } from 'node:test';
import { strict as assert } from 'node:assert';
import { spawn } from 'node:child_process';
import { fileURLToPath } from 'node:url';

const cliPath = fileURLToPath(new URL('../packages/tf-compose/bin/tf-verify-trace.mjs', import.meta.url));
const irPath = fileURLToPath(new URL('./fixtures/verify-ir.json', import.meta.url));
const manifestPath = fileURLToPath(new URL('./fixtures/manifest-limited.json', import.meta.url));
const okTracePath = fileURLToPath(new URL('./fixtures/trace-ok.jsonl', import.meta.url));
const deniedTracePath = fileURLToPath(new URL('./fixtures/trace-denied.jsonl', import.meta.url));
const unknownTracePath = fileURLToPath(new URL('./fixtures/trace-unknown.jsonl', import.meta.url));
const catalogPath = fileURLToPath(new URL('../packages/tf-l0-spec/spec/catalog.json', import.meta.url));

function canonicalJson(value) {
  if (Array.isArray(value)) {
    return '[' + value.map(canonicalJson).join(',') + ']';
  }
  if (value && typeof value === 'object') {
    const keys = Object.keys(value).sort();
    return '{' + keys.map((key) => `${JSON.stringify(key)}:${canonicalJson(value[key])}`).join(',') + '}';
  }
  return JSON.stringify(value);
}

async function runCli(args) {
  return new Promise((resolve, reject) => {
    const child = spawn(process.execPath, [cliPath, ...args], {
      stdio: ['ignore', 'pipe', 'pipe'],
    });

    let stdout = '';
    let stderr = '';

    child.stdout.setEncoding('utf8');
    child.stderr.setEncoding('utf8');

    child.stdout.on('data', (chunk) => {
      stdout += chunk;
    });

    child.stderr.on('data', (chunk) => {
      stderr += chunk;
    });

    child.on('error', reject);
    child.on('close', (code) => {
      resolve({ code, stdout, stderr });
    });
  });
}

test('passes for known prims without manifest', async () => {
  const { code, stdout, stderr } = await runCli(['--ir', irPath, '--trace', okTracePath]);
  assert.equal(code, 0, stderr);
  const result = JSON.parse(stdout.trim());
  assert.equal(stdout.trim(), canonicalJson(result));
  assert.equal(result.ok, true);
  assert.deepEqual(result.issues, []);
  assert.deepEqual(result.counts, {
    records: 2,
    unknown_prims: 0,
    denied_writes: 0,
  });
});

test('passes for known prims with catalog mapping', async () => {
  const { code, stdout, stderr } = await runCli([
    '--ir', irPath,
    '--trace', okTracePath,
    '--catalog', catalogPath,
  ]);
  assert.equal(code, 0, stderr);
  const result = JSON.parse(stdout.trim());
  assert.equal(stdout.trim(), canonicalJson(result));
  assert.equal(result.ok, true);
  assert.deepEqual(result.issues, []);
  assert.deepEqual(result.counts, {
    records: 2,
    unknown_prims: 0,
    denied_writes: 0,
  });
});

test('reports unknown prims', async () => {
  const { code, stdout } = await runCli(['--ir', irPath, '--trace', unknownTracePath]);
  assert.equal(code, 1);
  const result = JSON.parse(stdout.trim());
  assert.equal(stdout.trim(), canonicalJson(result));
  assert.equal(result.ok, false);
  assert.ok(result.issues.includes('unknown prim: tf:resource/unknown@1'));
  assert.equal(result.counts.unknown_prims, 1);
});

test('denies writes outside manifest prefixes', async () => {
  const { code, stdout } = await runCli([
    '--ir', irPath,
    '--trace', deniedTracePath,
    '--manifest', manifestPath,
    '--catalog', catalogPath,
  ]);
  assert.equal(code, 1);
  const result = JSON.parse(stdout.trim());
  assert.equal(stdout.trim(), canonicalJson(result));
  assert.equal(result.ok, false);
  assert.ok(result.issues.includes('write denied: res://kv/blocked/item'));
  assert.equal(result.counts.denied_writes, 1);
});
