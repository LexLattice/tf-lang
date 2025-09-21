import test from 'node:test';
import assert from 'node:assert/strict';
import { readFile } from 'node:fs/promises';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { spawn } from 'node:child_process';

const { parseDSL } = await import('../packages/tf-compose/src/parser.mjs');
const { checkAuthorize } = await import('../packages/tf-l0-check/src/authorize.mjs');

const __dirname = path.dirname(fileURLToPath(import.meta.url));
const repoRoot = path.resolve(__dirname, '..');
const catalogPath = path.resolve(repoRoot, 'packages/tf-l0-spec/spec/catalog.json');
const rulesPath = path.resolve(repoRoot, 'packages/tf-l0-check/rules/authorize-scopes.json');

async function loadJson(target) {
  const contents = await readFile(target, 'utf8');
  return JSON.parse(contents);
}

const [catalog, rules] = await Promise.all([
  loadJson(catalogPath),
  loadJson(rulesPath)
]);

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

test('authorize region satisfies scope requirement', async () => {
  const src = await readFlow('examples/flows/auth_ok.tf');
  const ir = parseDSL(src);
  const verdict = checkAuthorize(ir, catalog, rules);

  assert.equal(verdict.ok, true);
  assert.deepEqual(verdict.reasons, []);
  assert.deepEqual(verdict.warnings, []);
});

test('mismatched authorize scope is flagged', async () => {
  const src = await readFlow('examples/flows/auth_wrong_scope.tf');
  const ir = parseDSL(src);
  const verdict = checkAuthorize(ir, catalog, rules);

  assert.equal(verdict.ok, false);
  assert.ok(verdict.reasons.some((reason) => reason.includes('scope mismatch')));
});

test('missing authorize region is flagged', async () => {
  const src = await readFlow('examples/flows/auth_missing.tf');
  const ir = parseDSL(src);
  const verdict = checkAuthorize(ir, catalog, rules);

  assert.equal(verdict.ok, false);
  assert.ok(verdict.reasons.some((reason) => reason.includes('requires Authorize')));
});

test('warn-unused option marks unused authorize scopes', async () => {
  const ir = parseDSL('authorize(scope="kms.sign"){ emit-metric(key="ok") }');
  const verdict = checkAuthorize(ir, catalog, rules, { warnUnused: true });

  assert.equal(verdict.ok, true);
  assert.deepEqual(verdict.reasons, []);
  assert.deepEqual(verdict.warnings, ['auth: unused authorize scope "kms.sign"']);
});

test('strict-warns option fails when warnings are present', async () => {
  const ir = parseDSL('authorize(scope="kms.sign"){ emit-metric(key="ok") }');
  const verdict = checkAuthorize(ir, catalog, rules, {
    warnUnused: true,
    strictWarnsFail: true
  });

  assert.equal(verdict.ok, false);
  assert.deepEqual(verdict.reasons, []);
  assert.deepEqual(verdict.warnings, ['auth: unused authorize scope "kms.sign"']);
});

test('auth policy CLI reports success for valid flow', async () => {
  const result = await runAuthCli(['check', 'examples/flows/auth_ok.tf']);

  assert.equal(result.code, 0);
  const parsed = JSON.parse(result.stdout);
  assert.equal(parsed.ok, true);
  assert.deepEqual(parsed.reasons, []);
  assert.deepEqual(parsed.warnings, []);
});

test('auth policy CLI exposes reasons on failure', async () => {
  const result = await runAuthCli(['check', 'examples/flows/auth_wrong_scope.tf']);

  assert.equal(result.code, 1);
  const parsed = JSON.parse(result.stdout);
  assert.equal(parsed.ok, false);
  assert.ok(parsed.reasons.some((reason) => reason.includes('scope mismatch')));
  assert.equal(Array.isArray(parsed.warnings), true);
});
