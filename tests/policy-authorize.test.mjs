import test from 'node:test';
import assert from 'node:assert/strict';
import { readFile, mkdtemp, writeFile } from 'node:fs/promises';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { tmpdir } from 'node:os';
import { spawn } from 'node:child_process';

const { parseDSL } = await import('../packages/tf-compose/src/parser.mjs');
const { checkAuthorize } = await import('../packages/tf-l0-check/src/authorize.mjs');

const __dirname = path.dirname(fileURLToPath(import.meta.url));
const repoRoot = path.resolve(__dirname, '..');
const catalogPath = path.resolve(repoRoot, 'packages/tf-l0-spec/spec/catalog.json');
const rulesPath = path.resolve(repoRoot, 'packages/tf-l0-check/rules/authorize-scopes.json');

async function loadJSON(filePath) {
  const contents = await readFile(filePath, 'utf8');
  return JSON.parse(contents);
}

const [catalog, rules] = await Promise.all([loadJSON(catalogPath), loadJSON(rulesPath)]);

async function readFlow(relativePath) {
  return readFile(path.resolve(repoRoot, relativePath), 'utf8');
}

async function runAuthCli(args, options = {}) {
  const cliPath = path.resolve(repoRoot, 'packages/tf-compose/bin/tf-policy-auth.mjs');
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

async function writeTempFlow(contents) {
  const dir = await mkdtemp(path.join(tmpdir(), 'tf-auth-'));
  const file = path.join(dir, 'flow.tf');
  await writeFile(file, contents, 'utf8');
  return file;
}

test('authorize checker passes when scope matches requirement', async () => {
  const src = await readFlow('examples/flows/auth_ok.tf');
  const ir = parseDSL(src);
  const verdict = checkAuthorize(ir, catalog, rules);

  assert.equal(verdict.ok, true);
  assert.deepEqual(verdict.reasons, []);
  assert.deepEqual(verdict.warnings, []);
});

test('authorize checker flags scope mismatch', async () => {
  const src = await readFlow('examples/flows/auth_wrong_scope.tf');
  const ir = parseDSL(src);
  const verdict = checkAuthorize(ir, catalog, rules);

  assert.equal(verdict.ok, false);
  assert.equal(verdict.reasons.some((msg) => msg.includes('scope mismatch for tf:security/sign-data@1')), true);
});

test('authorize checker requires authorize region for protected primitive', async () => {
  const src = await readFlow('examples/flows/auth_missing.tf');
  const ir = parseDSL(src);
  const verdict = checkAuthorize(ir, catalog, rules);

  assert.equal(verdict.ok, false);
  assert.equal(verdict.reasons.some((msg) => msg.includes('requires Authorize{scope in [kms.sign]}')), true);
});

test('authorize checker reports unused scopes when requested', async () => {
  const src = 'authorize(scope="kms.sign"){ emit-metric(key="ok") }';
  const ir = parseDSL(src);
  const verdict = checkAuthorize(ir, catalog, rules, { warnUnused: true });

  assert.equal(verdict.ok, true);
  assert.deepEqual(verdict.warnings, ['auth: unused authorize scope "kms.sign"']);
});

test('auth policy CLI succeeds on valid flow', async () => {
  const result = await runAuthCli(['check', 'examples/flows/auth_ok.tf']);

  assert.equal(result.code, 0);
  const parsed = JSON.parse(result.stdout);
  assert.equal(parsed.ok, true);
  assert.deepEqual(parsed.reasons, []);
  assert.deepEqual(parsed.warnings, []);
});

test('auth policy CLI reports scope mismatch', async () => {
  const result = await runAuthCli(['check', 'examples/flows/auth_wrong_scope.tf']);

  assert.equal(result.code, 1);
  const parsed = JSON.parse(result.stdout);
  assert.equal(parsed.ok, false);
  assert.equal(parsed.reasons.some((msg) => msg.includes('scope mismatch')), true);
});

test('auth policy CLI reports missing authorize region', async () => {
  const result = await runAuthCli(['check', 'examples/flows/auth_missing.tf']);

  assert.equal(result.code, 1);
  const parsed = JSON.parse(result.stdout);
  assert.equal(parsed.ok, false);
  assert.equal(parsed.reasons.some((msg) => msg.includes('requires Authorize')), true);
});

test('auth policy CLI warns on unused scopes when enabled', async () => {
  const tempFlow = await writeTempFlow('authorize(scope="kms.sign"){ emit-metric(key="ok") }');
  const relPath = path.relative(repoRoot, tempFlow);
  const result = await runAuthCli(['check', relPath, '--warn-unused']);

  assert.equal(result.code, 0);
  const parsed = JSON.parse(result.stdout);
  assert.equal(parsed.ok, true);
  assert.deepEqual(parsed.warnings, ['auth: unused authorize scope "kms.sign"']);
});

test('auth policy CLI treats warnings as failures when strict', async () => {
  const tempFlow = await writeTempFlow('authorize(scope="kms.sign"){ emit-metric(key="ok") }');
  const relPath = path.relative(repoRoot, tempFlow);
  const result = await runAuthCli(['check', relPath, '--warn-unused', '--strict-warns']);

  assert.equal(result.code, 1);
  const parsed = JSON.parse(result.stdout);
  assert.equal(parsed.ok, false);
  assert.deepEqual(parsed.warnings, ['auth: unused authorize scope "kms.sign"']);
});
