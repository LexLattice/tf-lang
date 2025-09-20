import test from 'node:test';
import assert from 'node:assert/strict';
import { execFile } from 'node:child_process';
import { promisify } from 'node:util';
import path from 'node:path';
import { fileURLToPath } from 'node:url';

const execFileAsync = promisify(execFile);

const __dirname = path.dirname(fileURLToPath(import.meta.url));
const repoRoot = path.resolve(__dirname, '..');

async function runPolicy(flowPath, extraArgs = []) {
  try {
    const result = await execFileAsync(
      'node',
      ['packages/tf-compose/bin/tf-policy.mjs', 'check', flowPath, ...extraArgs],
      { cwd: repoRoot }
    );
    return { code: 0, stdout: result.stdout };
  } catch (error) {
    return { code: error.code ?? 1, stdout: error.stdout ?? '' };
  }
}

function parseOutput(stdout) {
  try {
    return JSON.parse(stdout);
  } catch (err) {
    assert.fail(`Failed to parse JSON output: ${err?.message || err}`);
  }
}

test('txn policy passes for idempotent writes inside txn', async () => {
  const { code, stdout } = await runPolicy('examples/flows/txn_ok.tf');
  assert.equal(code, 0);
  const payload = parseOutput(stdout);
  assert.equal(payload.ok, true);
  assert.deepEqual(payload.reasons, []);
});

test('txn policy flags missing idempotency key inside txn', async () => {
  const { code, stdout } = await runPolicy('examples/flows/txn_fail_missing_key.tf');
  assert.notEqual(code, 0);
  const payload = parseOutput(stdout);
  assert.equal(payload.ok, false);
  assert.ok(payload.reasons.some((r) => r.includes('requires idempotency_key')));
});

test('txn policy forbids writes outside txn when flagged', async () => {
  const { code, stdout } = await runPolicy('examples/flows/write_outside_txn.tf', ['--forbid-outside']);
  assert.notEqual(code, 0);
  const payload = parseOutput(stdout);
  assert.equal(payload.ok, false);
  assert.ok(payload.reasons.some((r) => r.includes('outside transaction')));
});
