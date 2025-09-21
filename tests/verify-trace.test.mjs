import { test } from 'node:test';
import { strict as assert } from 'node:assert';
import { spawn } from 'node:child_process';
import { fileURLToPath } from 'node:url';

const cliPath = fileURLToPath(new URL('../packages/tf-compose/bin/tf-verify-trace.mjs', import.meta.url));
const irPath = fileURLToPath(new URL('./fixtures/verify-trace.ir.json', import.meta.url));
const traceOkPath = fileURLToPath(new URL('./fixtures/trace-ok.jsonl', import.meta.url));
const traceDeniedPath = fileURLToPath(new URL('./fixtures/trace-denied.jsonl', import.meta.url));
const traceUnknownPath = fileURLToPath(new URL('./fixtures/trace-unknown.jsonl', import.meta.url));
const manifestPath = fileURLToPath(new URL('./fixtures/manifest-allowed.json', import.meta.url));
const catalogPath = fileURLToPath(new URL('../packages/tf-l0-spec/spec/catalog.json', import.meta.url));

function runCli(args) {
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

test('accepts traces whose primitives appear in the IR', async () => {
  const { code, stdout, stderr } = await runCli(['--ir', irPath, '--trace', traceOkPath]);
  assert.equal(code, 0, stderr);
  const payload = JSON.parse(stdout);
  assert.equal(payload.ok, true);
  assert.deepEqual(payload.issues, []);
  assert.equal(payload.counts.records, 2);
  assert.equal(payload.counts.unknown_prims, 0);
  assert.equal(payload.counts.denied_writes, 0);
  assert.equal(stdout.trim(), canonicalJson(payload));
});

test('flags unknown primitives from the trace', async () => {
  const { code, stdout } = await runCli(['--ir', irPath, '--trace', traceUnknownPath]);
  assert.equal(code, 1);
  const payload = JSON.parse(stdout);
  assert.equal(payload.ok, false);
  assert.ok(payload.issues.includes('unknown prim: tf:resource/unknown@1'));
  assert.equal(payload.counts.unknown_prims, 1);
  assert.equal(stdout.trim(), canonicalJson(payload));
});

test('denies writes outside manifest prefixes', async () => {
  const { code, stdout } = await runCli([
    '--ir', irPath,
    '--trace', traceDeniedPath,
    '--manifest', manifestPath,
  ]);
  assert.equal(code, 1);
  const payload = JSON.parse(stdout);
  assert.equal(payload.ok, false);
  assert.ok(payload.issues.includes('write denied: res://kv/blocked/item'));
  assert.equal(payload.counts.denied_writes, 1);
  assert.equal(stdout.trim(), canonicalJson(payload));
});

test('catalog is optional for identifying writes', async () => {
  const withoutCatalog = await runCli(['--ir', irPath, '--trace', traceOkPath]);
  assert.equal(withoutCatalog.code, 0, withoutCatalog.stderr);
  const withCatalog = await runCli([
    '--ir', irPath,
    '--trace', traceOkPath,
    '--catalog', catalogPath,
  ]);
  assert.equal(withCatalog.code, 0, withCatalog.stderr);
  assert.equal(withoutCatalog.stdout.trim(), withCatalog.stdout.trim());
  const payload = JSON.parse(withCatalog.stdout);
  assert.equal(payload.ok, true);
  assert.equal(withCatalog.stdout.trim(), canonicalJson(payload));
});
