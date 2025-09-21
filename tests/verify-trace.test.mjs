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
const bareIrPath = fileURLToPath(new URL('./fixtures/verify-ir-bare.json', import.meta.url));
const bareTracePath = fileURLToPath(new URL('./fixtures/trace-bare.jsonl', import.meta.url));
const canonicalTracePath = fileURLToPath(new URL('./fixtures/trace-canonical-write.jsonl', import.meta.url));
const canonicalMismatchTracePath = fileURLToPath(new URL('./fixtures/trace-canonical-mismatch.jsonl', import.meta.url));
const canonicalMismatchReorderedTracePath = fileURLToPath(
  new URL('./fixtures/trace-canonical-mismatch-reordered.jsonl', import.meta.url),
);
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
    provenance_mismatches: 0,
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
    provenance_mismatches: 0,
  });
});

test('allows writes when manifest patterns match', async () => {
  const { code, stdout, stderr } = await runCli([
    '--ir', irPath,
    '--trace', okTracePath,
    '--manifest', manifestPath,
    '--catalog', catalogPath,
  ]);
  assert.equal(code, 0, stderr);
  const result = JSON.parse(stdout.trim());
  assert.equal(stdout.trim(), canonicalJson(result));
  assert.equal(result.ok, true);
  assert.deepEqual(result.issues, []);
  assert.equal(result.counts.denied_writes, 0);
  assert.equal(result.counts.provenance_mismatches, 0);
});

test('reports unknown prims', async () => {
  const { code, stdout } = await runCli(['--ir', irPath, '--trace', unknownTracePath]);
  assert.equal(code, 1);
  const result = JSON.parse(stdout.trim());
  assert.equal(stdout.trim(), canonicalJson(result));
  assert.equal(result.ok, false);
  assert.ok(result.issues.includes('unknown prim: tf:resource/unknown@1'));
  assert.equal(result.counts.unknown_prims, 1);
  assert.equal(result.counts.provenance_mismatches, 0);
});

test('requires canonical match when provided', async () => {
  const { code, stdout } = await runCli([
    '--ir', irPath,
    '--trace', canonicalMismatchTracePath,
  ]);
  assert.equal(code, 1);
  const result = JSON.parse(stdout.trim());
  assert.equal(stdout.trim(), canonicalJson(result));
  assert.equal(result.ok, false);
  assert.deepEqual(result.issues, [
    'unknown prim: tf:evil/write-object@1',
    'unknown prim: tf:resource/write-object@99',
  ]);
  assert.equal(result.counts.unknown_prims, 2);
  assert.equal(result.counts.provenance_mismatches, 0);
});

test('canonical mismatch results are deterministic across trace orderings', async () => {
  const first = await runCli(['--ir', irPath, '--trace', canonicalMismatchTracePath]);
  const second = await runCli(['--ir', irPath, '--trace', canonicalMismatchReorderedTracePath]);
  assert.equal(first.stdout.trim(), second.stdout.trim());
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
  assert.ok(result.issues.includes('write denied: res://kv/mybucket/blocked/item'));
  assert.equal(result.counts.denied_writes, 1);
  assert.equal(result.counts.provenance_mismatches, 0);
});

test('allows bare names when canonical is absent', async () => {
  const { code, stdout, stderr } = await runCli([
    '--ir', bareIrPath,
    '--trace', bareTracePath,
  ]);
  assert.equal(code, 0, stderr);
  const result = JSON.parse(stdout.trim());
  assert.equal(stdout.trim(), canonicalJson(result));
  assert.equal(result.ok, true);
  assert.deepEqual(result.issues, []);
});

test('canonical trace is unknown without catalog when IR only lists bare name', async () => {
  const { code, stdout } = await runCli([
    '--ir', bareIrPath,
    '--trace', canonicalTracePath,
  ]);
  assert.equal(code, 1);
  const result = JSON.parse(stdout.trim());
  assert.equal(stdout.trim(), canonicalJson(result));
  assert.equal(result.ok, false);
  assert.deepEqual(result.issues, ['unknown prim: tf:resource/write-object@1']);
});

test('catalog provides canonical mapping for bare IR prims', async () => {
  const { code, stdout, stderr } = await runCli([
    '--ir', bareIrPath,
    '--trace', canonicalTracePath,
    '--catalog', catalogPath,
  ]);
  assert.equal(code, 0, stderr);
  const result = JSON.parse(stdout.trim());
  assert.equal(stdout.trim(), canonicalJson(result));
  assert.equal(result.ok, true);
  assert.deepEqual(result.issues, []);
});
