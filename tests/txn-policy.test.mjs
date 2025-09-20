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

async function runPolicyCli(args) {
  const cliPath = path.resolve(repoRoot, 'packages/tf-compose/bin/tf-policy.mjs');
  const child = spawn(process.execPath, [cliPath, ...args], {
    cwd: repoRoot,
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
  assert.ok(verdict.reasons.some((r) => r.includes('requires idempotency_key')));
});

test('policy CLI forbids writes outside txn when requested', async () => {
  const result = await runPolicyCli([
    'check',
    'examples/flows/write_outside_txn.tf',
    '--forbid-outside'
  ]);

  assert.notEqual(result.code, 0);
  const parsed = JSON.parse(result.stdout);
  assert.equal(parsed.ok, false);
  assert.ok(parsed.reasons.some((r) => r.includes('outside transaction')));
});
