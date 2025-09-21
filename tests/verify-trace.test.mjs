import { test } from 'node:test';
import { strict as assert } from 'node:assert';
import { spawn } from 'node:child_process';
import { fileURLToPath } from 'node:url';

const scriptPath = fileURLToPath(new URL('../packages/tf-compose/bin/tf-verify-trace.mjs', import.meta.url));
const irPath = fileURLToPath(new URL('./fixtures/verify-ir.json', import.meta.url));
const traceOkPath = fileURLToPath(new URL('./fixtures/trace-ok.jsonl', import.meta.url));
const traceUnknownPath = fileURLToPath(new URL('./fixtures/trace-unknown.jsonl', import.meta.url));
const traceDeniedPath = fileURLToPath(new URL('./fixtures/trace-denied.jsonl', import.meta.url));
const manifestPath = fileURLToPath(new URL('./fixtures/verify-manifest.json', import.meta.url));
const catalogPath = fileURLToPath(new URL('../packages/tf-l0-spec/spec/catalog.json', import.meta.url));

function runCli(args) {
  return new Promise((resolve, reject) => {
    const child = spawn(process.execPath, [scriptPath, ...args], {
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

test('ok case without manifest', async () => {
  const { code, stdout, stderr } = await runCli([
    '--ir',
    irPath,
    '--trace',
    traceOkPath,
  ]);
  assert.equal(code, 0, stderr);
  const result = JSON.parse(stdout.trim());
  assert.equal(result.ok, true);
  assert.deepEqual(result.issues, []);
  assert.equal(result.counts.records, 2);
  assert.equal(result.counts.unknown_prims, 0);
  assert.equal(result.counts.denied_writes, 0);
  assert.equal(stdout.trim(), canonicalJson(result));
});

test('catalog optionality produces same output', async () => {
  const base = await runCli([
    '--ir',
    irPath,
    '--trace',
    traceOkPath,
  ]);
  const withCatalog = await runCli([
    '--ir',
    irPath,
    '--trace',
    traceOkPath,
    '--catalog',
    catalogPath,
  ]);

  assert.equal(base.code, 0, base.stderr);
  assert.equal(withCatalog.code, 0, withCatalog.stderr);
  assert.equal(base.stdout, withCatalog.stdout);
});

test('flags unknown primitives', async () => {
  const { code, stdout } = await runCli([
    '--ir',
    irPath,
    '--trace',
    traceUnknownPath,
  ]);
  assert.equal(code, 1);
  const result = JSON.parse(stdout.trim());
  assert.equal(result.ok, false);
  assert.ok(result.issues.includes('unknown prim: tf:resource/unknown@1'));
  assert.equal(result.counts.records, 1);
  assert.equal(result.counts.unknown_prims, 1);
  assert.equal(result.counts.denied_writes, 0);
  assert.equal(stdout.trim(), canonicalJson(result));
});

test('denies writes outside manifest prefixes', async () => {
  const { code, stdout } = await runCli([
    '--ir',
    irPath,
    '--trace',
    traceDeniedPath,
    '--manifest',
    manifestPath,
  ]);
  assert.equal(code, 1);
  const result = JSON.parse(stdout.trim());
  assert.equal(result.ok, false);
  assert.ok(result.issues.includes('write denied: res://kv/blocked/item'));
  assert.equal(result.counts.records, 1);
  assert.equal(result.counts.unknown_prims, 0);
  assert.equal(result.counts.denied_writes, 1);
  assert.equal(stdout.trim(), canonicalJson(result));
});
