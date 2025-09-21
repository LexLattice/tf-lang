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

async function loadJson(targetPath) {
  const contents = await readFile(targetPath, 'utf8');
  return JSON.parse(contents);
}

const [catalog, rules] = await Promise.all([
  loadJson(catalogPath),
  loadJson(rulesPath)
]);

async function readFlow(relativePath) {
  const fullPath = path.resolve(repoRoot, relativePath);
  return readFile(fullPath, 'utf8');
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

function parseFlow(irSource) {
  return parseDSL(irSource);
}

test('authorize check passes with matching scope', async () => {
  const src = await readFlow('examples/flows/auth_ok.tf');
  const ir = parseFlow(src);
  const verdict = checkAuthorize(ir, catalog, rules);

  assert.equal(verdict.ok, true);
  assert.deepEqual(verdict.reasons, []);
});

test('authorize check flags scope mismatch', async () => {
  const src = await readFlow('examples/flows/auth_wrong_scope.tf');
  const ir = parseFlow(src);
  const verdict = checkAuthorize(ir, catalog, rules);

  assert.equal(verdict.ok, false);
  assert.ok(verdict.reasons.some((reason) => reason.includes('scope mismatch')));
});

test('authorize check flags missing authorize region', async () => {
  const src = await readFlow('examples/flows/auth_missing.tf');
  const ir = parseFlow(src);
  const verdict = checkAuthorize(ir, catalog, rules);

  assert.equal(verdict.ok, false);
  assert.ok(verdict.reasons.some((reason) => reason.includes('requires Authorize')));
});

test('authorize check warns on unused scope when requested', async () => {
  const ir = parseFlow('authorize(scope="kms.sign"){ emit-metric(key="ok") }');
  const verdict = checkAuthorize(ir, catalog, rules, { warnUnused: true });

  assert.equal(verdict.ok, true);
  assert.deepEqual(verdict.reasons, []);
  assert.ok(verdict.warnings.includes('auth: unused authorize scope "kms.sign"'));
});

test('authorize check treats warnings as failures in strict mode', async () => {
  const ir = parseFlow('authorize(scope="kms.sign"){ emit-metric(key="ok") }');
  const verdict = checkAuthorize(ir, catalog, rules, { warnUnused: true, strictWarnsFail: true });

  assert.equal(verdict.ok, false);
  assert.ok(verdict.warnings.includes('auth: unused authorize scope "kms.sign"'));
});

test('authorize CLI surfaces results and exit codes', async () => {
  const okResult = await runAuthCli(['check', 'examples/flows/auth_ok.tf']);
  assert.equal(okResult.code, 0);
  const okParsed = JSON.parse(okResult.stdout);
  assert.equal(okParsed.ok, true);
  assert.deepEqual(okParsed.reasons, []);

  const mismatchResult = await runAuthCli(['check', 'examples/flows/auth_wrong_scope.tf']);
  assert.equal(mismatchResult.code, 1);
  const mismatchParsed = JSON.parse(mismatchResult.stdout);
  assert.equal(mismatchParsed.ok, false);
  assert.ok(mismatchParsed.reasons.some((reason) => reason.includes('scope mismatch')));

  const warnResult = await runAuthCli(['check', 'examples/flows/auth_ok.tf', '--warn-unused']);
  assert.equal(warnResult.code, 0);
  const warnParsed = JSON.parse(warnResult.stdout);
  assert.equal(warnParsed.ok, true);
  assert.deepEqual(warnParsed.reasons, []);
  assert.deepEqual(warnParsed.warnings, []);
});
