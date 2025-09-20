import test from 'node:test';
import assert from 'node:assert/strict';
import { readFile } from 'node:fs/promises';
import { execFile } from 'node:child_process';
import { promisify } from 'node:util';

import { parseDSL } from '../packages/tf-compose/src/parser.mjs';
import { checkTransactions } from '../packages/tf-l0-check/src/txn.mjs';

const exec = promisify(execFile);

async function loadCatalog() {
  try {
    const raw = await readFile('packages/tf-l0-spec/spec/catalog.json', 'utf8');
    return JSON.parse(raw);
  } catch {
    return { primitives: [] };
  }
}

test('transaction policy accepts idempotent writes', async () => {
  const src = await readFile('examples/flows/txn_ok.tf', 'utf8');
  const ir = parseDSL(src);
  const verdict = checkTransactions(ir, await loadCatalog());
  assert.equal(verdict.ok, true);
  assert.deepEqual(verdict.reasons, []);
});

test('transaction policy rejects missing idempotency key', async () => {
  const src = await readFile('examples/flows/txn_fail_missing_key.tf', 'utf8');
  const ir = parseDSL(src);
  const verdict = checkTransactions(ir, await loadCatalog());
  assert.equal(verdict.ok, false);
  assert(verdict.reasons.some(r => r.includes('requires idempotency_key')));
});

test('policy CLI flags writes outside transactions when forbidden', async () => {
  try {
    await exec('node', [
      'packages/tf-compose/bin/tf-policy.mjs',
      'check',
      'examples/flows/write_outside_txn.tf',
      '--forbid-outside'
    ]);
    assert.fail('CLI should fail for writes outside transactions');
  } catch (err) {
    const stdout = err?.stdout || '';
    const payload = JSON.parse(stdout);
    assert.equal(payload.ok, false);
    assert(payload.reasons.some(r => r.includes('outside transaction')));
  }
});
