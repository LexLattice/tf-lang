import test from 'node:test';
import assert from 'node:assert/strict';
import { readFile, writeFile, mkdtemp } from 'node:fs/promises';
import path from 'node:path';
import os from 'node:os';
import { fileURLToPath } from 'node:url';
import { spawn } from 'node:child_process';

const { parseDSL } = await import('../packages/tf-compose/src/parser.mjs');
const { checkAuthorize } = await import('../packages/tf-l0-check/src/authorize.mjs');

const __dirname = path.dirname(fileURLToPath(import.meta.url));
const repoRoot = path.resolve(__dirname, '..');

async function loadCatalog() {
  const catalogPath = path.resolve(repoRoot, 'packages/tf-l0-spec/spec/catalog.json');
  const contents = await readFile(catalogPath, 'utf8');
  return JSON.parse(contents);
}

async function loadRules() {
  const rulesPath = path.resolve(repoRoot, 'packages/tf-l0-check/rules/authorize-scopes.json');
  const contents = await readFile(rulesPath, 'utf8');
  return JSON.parse(contents);
}

const [catalog, rules] = await Promise.all([loadCatalog(), loadRules()]);

async function readFlow(relativePath) {
  return readFile(path.resolve(repoRoot, relativePath), 'utf8');
}

async function runAuthCli(args) {
  const cliPath = path.resolve(repoRoot, 'packages/tf-compose/bin/tf-policy-auth.mjs');
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

function parseCliOutput(stdout) {
  try {
    return JSON.parse(stdout);
  } catch (err) {
    throw new Error(`Failed to parse CLI output: ${stdout}\n${err}`);
  }
}

test('authorize check passes when scope matches', async () => {
  const src = await readFlow('examples/flows/auth_ok.tf');
  const ir = parseDSL(src);
  const verdict = checkAuthorize(ir, catalog, rules);

  assert.equal(verdict.ok, true);
  assert.deepEqual(verdict.reasons, []);
});

test('authorize check detects wrong scope', async () => {
  const src = await readFlow('examples/flows/auth_wrong_scope.tf');
  const ir = parseDSL(src);
  const verdict = checkAuthorize(ir, catalog, rules);

  assert.equal(verdict.ok, false);
  assert.equal(verdict.reasons.length, 1);
  assert.match(verdict.reasons[0], /scope mismatch/);
});

test('authorize check detects missing authorize region', async () => {
  const src = await readFlow('examples/flows/auth_missing.tf');
  const ir = parseDSL(src);
  const verdict = checkAuthorize(ir, catalog, rules);

  assert.equal(verdict.ok, false);
  assert.equal(verdict.reasons.length, 1);
  assert.match(verdict.reasons[0], /requires Authorize/);
});

test('CLI reports unused authorize scopes as warnings', async () => {
  const tmpDir = await mkdtemp(path.join(os.tmpdir(), 'tf-auth-'));
  const flowPath = path.join(tmpDir, 'unused.tf');
  await writeFile(flowPath, 'authorize(scope="kms.sign"){ emit-metric(key="foo") }', 'utf8');

  const result = await runAuthCli(['check', flowPath, '--warn-unused']);
  assert.equal(result.code, 0);

  const parsed = parseCliOutput(result.stdout);
  assert.equal(parsed.ok, true);
  assert.deepEqual(parsed.reasons, []);
  assert.equal(parsed.warnings.length, 1);
  assert.match(parsed.warnings[0], /unused authorize scope/);
});

test('CLI treats warnings as failures when strict flag is set', async () => {
  const tmpDir = await mkdtemp(path.join(os.tmpdir(), 'tf-auth-'));
  const flowPath = path.join(tmpDir, 'unused-strict.tf');
  await writeFile(flowPath, 'authorize(scope="kms.sign"){ emit-metric(key="foo") }', 'utf8');

  const result = await runAuthCli(['check', flowPath, '--warn-unused', '--strict-warns']);
  assert.equal(result.code, 1);

  const parsed = parseCliOutput(result.stdout);
  assert.equal(parsed.ok, false);
  assert.deepEqual(parsed.reasons, []);
  assert.equal(parsed.warnings.length, 1);
  assert.match(parsed.warnings[0], /unused authorize scope/);
});
