// @tf-test kind=product area=policy speed=fast deps=node

import test from 'node:test';
import assert from 'node:assert/strict';
import { readFile, writeFile, mkdir } from 'node:fs/promises';
import { randomUUID } from 'node:crypto';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { spawn } from 'node:child_process';

const __dirname = path.dirname(fileURLToPath(import.meta.url));
const repoRoot = path.resolve(__dirname, '..');
const policyTestDir = path.join(repoRoot, 'out/0.4/check/policy/test');
await mkdir(policyTestDir, { recursive: true });

const catalogPath = path.join(repoRoot, 'packages/tf-l0-spec/spec/catalog.json');
const rulesPath = path.join(repoRoot, 'packages/tf-l0-check/rules/authorize-scopes.json');

const [{ parseDSL }, { checkAuthorize }] = await Promise.all([
  import('../packages/tf-compose/src/parser.mjs'),
  import('../packages/tf-l0-check/src/authorize.mjs')
]);

async function loadJson(targetPath) {
  const contents = await readFile(targetPath, 'utf8');
  return JSON.parse(contents);
}

const [catalog, rules] = await Promise.all([
  loadJson(catalogPath),
  loadJson(rulesPath)
]);

async function runAuthCli(args, options = {}) {
  const cliPath = path.join(repoRoot, 'packages/tf-compose/bin/tf-policy-auth.mjs');
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

async function captureCliJson(name, args, options = {}) {
  const result = await runAuthCli(args, options);
  if (result.stdout.length > 0) {
    const target = path.join(policyTestDir, `${name}.json`);
    await writeFile(target, result.stdout, 'utf8');
    try {
      result.payload = JSON.parse(result.stdout);
    } catch (err) {
      throw new Error(`Failed to parse CLI JSON for ${name}: ${err.message}`);
    }
  }
  return result;
}

function parseFlow(source) {
  return parseDSL(source);
}

test('authorize checker accepts matching scope', async () => {
  const src = await readFile(path.join(repoRoot, 'examples/flows/auth_ok.tf'), 'utf8');
  const verdict = checkAuthorize(parseFlow(src), catalog, rules);

  assert.equal(verdict.ok, true);
  assert.deepEqual(verdict.reasons, []);
  assert.deepEqual(verdict.warnings, []);
});

test('authorize checker flags scope mismatch', async () => {
  const src = await readFile(path.join(repoRoot, 'examples/flows/auth_wrong_scope.tf'), 'utf8');
  const verdict = checkAuthorize(parseFlow(src), catalog, rules);

  assert.equal(verdict.ok, false);
  assert.ok(verdict.reasons.some((reason) => reason.includes('scope mismatch')));
});

test('authorize checker flags missing authorize region', async () => {
  const src = await readFile(path.join(repoRoot, 'examples/flows/auth_missing.tf'), 'utf8');
  const verdict = checkAuthorize(parseFlow(src), catalog, rules);

  assert.equal(verdict.ok, false);
  assert.ok(verdict.reasons.some((reason) => reason.includes('requires Authorize')));
});

test('authorize checker warns on unused scopes individually', async () => {
  const flow = 'authorize(scope="kms.sign,kms.decrypt"){ sign-data(key="k1") }';
  const verdict = checkAuthorize(parseFlow(flow), catalog, rules, { warnUnused: true });

  assert.equal(verdict.ok, true);
  assert.deepEqual(verdict.reasons, []);
  assert.deepEqual(verdict.warnings, ['auth: unused authorize scope "kms.decrypt"']);
});

test('CLI: ok flow succeeds with empty warnings', async () => {
  const result = await captureCliJson('ok', ['check', 'examples/flows/auth_ok.tf']);
  assert.equal(result.code, 0);
  assert.deepEqual(result.payload, { ok: true, reasons: [], warnings: [] });
});

test('CLI: wrong scope fails with reason', async () => {
  const result = await captureCliJson('wrong_scope', ['check', 'examples/flows/auth_wrong_scope.tf']);
  assert.equal(result.code, 1);
  assert.equal(result.payload.ok, false);
  assert.ok(result.payload.reasons.some((reason) => reason.includes('kms.sign')));
});

test('CLI: missing authorize region fails', async () => {
  const result = await captureCliJson('missing', ['check', 'examples/flows/auth_missing.tf']);
  assert.equal(result.code, 1);
  assert.equal(result.payload.ok, false);
  assert.ok(result.payload.reasons.some((reason) => reason.includes('Authorize')));
});

test('CLI: warn-unused surfaces warnings and strict mode exit', async () => {
  const flowSource = 'authorize(scope="kms.sign,kms.decrypt"){ sign-data(key="k1") }';
  const tempFlowPath = path.join(policyTestDir, `${randomUUID()}.tf`);
  await writeFile(tempFlowPath, flowSource, 'utf8');

  const warnResult = await captureCliJson('warn_unused', ['check', tempFlowPath, '--warn-unused']);
  assert.equal(warnResult.code, 0);
  assert.equal(warnResult.payload.ok, true);
  assert.deepEqual(warnResult.payload.warnings, ['auth: unused authorize scope "kms.decrypt"']);

  const strictResult = await captureCliJson('warn_unused_strict', ['check', tempFlowPath, '--warn-unused', '--strict-warns']);
  assert.equal(strictResult.code, 1);
  assert.equal(strictResult.payload.ok, false);
  assert.deepEqual(strictResult.payload.warnings, ['auth: unused authorize scope "kms.decrypt"']);
});

test('CLI: malformed rules file fails with exit code 1', async () => {
  const invalidRulesPath = path.join(policyTestDir, `${randomUUID()}-invalid-rules.json`);
  await writeFile(invalidRulesPath, JSON.stringify({ 'tf:security/sign-data@1': 'kms.sign' }), 'utf8');

  const result = await runAuthCli(['check', 'examples/flows/auth_ok.tf', '--rules', invalidRulesPath]);
  assert.equal(result.code, 1);
  assert.equal(result.stdout.trim(), '');
  assert.ok(result.stderr.trim().startsWith('Invalid authorize'));
});
