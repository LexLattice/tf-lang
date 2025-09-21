import { test } from 'node:test';
import { strict as assert } from 'node:assert';
import { spawn } from 'node:child_process';
import { fileURLToPath } from 'node:url';

const scriptPath = fileURLToPath(new URL('../packages/tf-compose/bin/tf-verify-trace.mjs', import.meta.url));
const irPath = fileURLToPath(new URL('./fixtures/verify-ir.json', import.meta.url));
const traceOkPath = fileURLToPath(new URL('./fixtures/trace-ok.jsonl', import.meta.url));
const traceUnknownPath = fileURLToPath(new URL('./fixtures/trace-unknown.jsonl', import.meta.url));
const traceDeniedPath = fileURLToPath(new URL('./fixtures/trace-denied.jsonl', import.meta.url));
const manifestPath = fileURLToPath(new URL('./fixtures/manifest-allowed.json', import.meta.url));
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

test('ok trace passes with and without catalog', async () => {
  const baseArgs = ['--ir', irPath, '--trace', traceOkPath];
  const first = await runCli(baseArgs);
  assert.equal(first.code, 0, first.stderr);
  const firstResult = JSON.parse(first.stdout);
  assert.equal(firstResult.ok, true);
  assert.deepEqual(firstResult.issues, []);
  assert.deepEqual(firstResult.counts, {
    records: 2,
    unknown_prims: 0,
    denied_writes: 0,
  });
  assert.equal(first.stdout.trim(), canonicalJson(firstResult));

  const second = await runCli([...baseArgs, '--catalog', catalogPath]);
  assert.equal(second.code, 0, second.stderr);
  const secondResult = JSON.parse(second.stdout);
  assert.equal(secondResult.ok, true);
  assert.deepEqual(secondResult.issues, []);
  assert.deepEqual(secondResult.counts, {
    records: 2,
    unknown_prims: 0,
    denied_writes: 0,
  });
  assert.equal(second.stdout.trim(), canonicalJson(secondResult));
});

test('reports unknown prims', async () => {
  const result = await runCli(['--ir', irPath, '--trace', traceUnknownPath]);
  assert.equal(result.code, 1, result.stderr);
  const parsed = JSON.parse(result.stdout);
  assert.equal(parsed.ok, false);
  assert.deepEqual(parsed.issues, ['unknown prim: tf:resource/unknown@1']);
  assert.equal(parsed.counts.unknown_prims, 1);
  assert.equal(parsed.counts.records, 1);
  assert.equal(parsed.counts.denied_writes, 0);
  assert.equal(result.stdout.trim(), canonicalJson(parsed));
});

test('denies writes outside manifest prefixes', async () => {
  const result = await runCli([
    '--ir',
    irPath,
    '--trace',
    traceDeniedPath,
    '--manifest',
    manifestPath,
  ]);
  assert.equal(result.code, 1, result.stderr);
  const parsed = JSON.parse(result.stdout);
  assert.equal(parsed.ok, false);
  assert.deepEqual(parsed.issues, ['write denied: res://kv/blocked/item']);
  assert.equal(parsed.counts.denied_writes, 1);
  assert.equal(parsed.counts.records, 1);
  assert.equal(parsed.counts.unknown_prims, 0);
  assert.equal(result.stdout.trim(), canonicalJson(parsed));
});
