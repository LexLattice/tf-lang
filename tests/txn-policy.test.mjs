// @tf-test kind=product area=policy speed=medium deps=node
import test from 'node:test';
import assert from 'node:assert/strict';
import { readFile } from 'node:fs/promises';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { spawn } from 'node:child_process';

const { parseDSL } = await import('../packages/tf-compose/src/parser.mjs');
const { checkTransactions } = await import('../packages/tf-l0-check/src/txn.mjs');

const __dirname = path.dirname(fileURLToPath(import.meta.url));
const repoRoot = path.resolve(__dirname, '..');
const catalogPath = path.resolve(repoRoot, 'packages/tf-l0-spec/spec/catalog.json');

async function loadCatalog() {
  const contents = await readFile(catalogPath, 'utf8');
  return JSON.parse(contents);
}

const catalog = await loadCatalog();

async function readFlow(relativePath) {
  return readFile(path.resolve(repoRoot, relativePath), 'utf8');
}

async function runPolicyCli(args, options = {}) {
  const cliPath = path.resolve(repoRoot, 'packages/tf-compose/bin/tf-policy.mjs');
  const child = spawn(process.execPath, [cliPath, ...args], {
    cwd: options.cwd ?? repoRoot,
    stdio: ['ignore', 'pipe', 'pipe']
  });

  const stdoutChunks = [];
  const stderrChunks = [];

  child.stdout.on('data', (chunk) => stdoutChunks.push(chunk));
  child.stderr.on('data', (chunk) => stderrChunks.push(chunk));

  const code = await new Promise((resolve, reject) => {
    child.on('error', reject);
    child.on('close', resolve);
  });

  return {
    code,
    stdout: Buffer.concat(stdoutChunks).toString('utf8'),
    stderr: Buffer.concat(stderrChunks).toString('utf8')
  };
}

test('transaction writes inside txn require idempotency key', async () => {
  const src = await readFlow('examples/flows/txn_ok.tf');
  const ir = parseDSL(src);
  const verdict = checkTransactions(ir, catalog);

  assert.equal(verdict.ok, true);
  assert.deepEqual(verdict.reasons, []);
});

test('missing idempotency key in txn is flagged', async () => {
  const src = await readFlow('examples/flows/txn_fail_missing_key.tf');
  const ir = parseDSL(src);
  const verdict = checkTransactions(ir, catalog);

  assert.equal(verdict.ok, false);
  assert.deepEqual(verdict.reasons, [
    'txn: write-object requires idempotency_key or compare-and-swap'
  ]);
});

test('policy CLI forbids writes outside txn when requested', async () => {
  const result = await runPolicyCli([
    'check',
    'examples/flows/write_outside_txn.tf',
    '--forbid-outside'
  ]);

  assert.equal(result.code, 1);
  const parsed = JSON.parse(result.stdout);
  assert.equal(parsed.ok, false);
  assert.deepEqual(parsed.reasons, ['policy: write-object outside transaction']);
  assert.equal(result.stderr.includes('warn:'), false);
});

test('policy CLI warns and falls back when catalog is missing', async () => {
  const result = await runPolicyCli([
    'check',
    'examples/flows/write_outside_txn.tf',
    '--forbid-outside',
    '--catalog',
    'does-not-exist.json'
  ]);

  assert.equal(result.code, 1);
  assert.match(result.stderr, /warn: catalog not found or invalid/);
  assert.match(result.stderr, /warn: using name-based detection; supply --catalog to avoid false negatives/);
  const parsed = JSON.parse(result.stdout);
  assert.equal(parsed.ok, false);
  assert.deepEqual(parsed.reasons, ['policy: write-object outside transaction']);
});

test('policy CLI locates catalog when run from its own directory', async () => {
  const cliDir = path.resolve(repoRoot, 'packages/tf-compose/bin');
  const result = await runPolicyCli([
    'check',
    '../../../examples/flows/txn_ok.tf'
  ], { cwd: cliDir });

  assert.equal(result.code, 0);
  const parsed = JSON.parse(result.stdout);
  assert.equal(parsed.ok, true);
  assert.deepEqual(parsed.reasons, []);
});
