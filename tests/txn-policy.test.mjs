import test from 'node:test';
import assert from 'node:assert/strict';
import { readFile } from 'node:fs/promises';

const { parseDSL } = await import('../packages/tf-compose/src/parser.mjs');
const { checkTransactions } = await import('../packages/tf-l0-check/src/txn.mjs');

const catalog = JSON.parse(
  await readFile('packages/tf-l0-spec/spec/catalog.json', 'utf8')
);

async function loadFlow(path) {
  const src = await readFile(path, 'utf8');
  return parseDSL(src);
}

test('txn policy passes when writes are safe', async () => {
  const ir = await loadFlow('examples/flows/txn_ok.tf');
  const verdict = checkTransactions(ir, catalog);
  assert.equal(verdict.ok, true);
  assert.deepEqual(verdict.reasons, []);
});

test('missing idempotency_key inside txn fails', async () => {
  const ir = await loadFlow('examples/flows/txn_fail_missing_key.tf');
  const verdict = checkTransactions(ir, catalog);
  assert.equal(verdict.ok, false);
  assert(verdict.reasons.some(r => r.includes('requires idempotency_key')));
});

test('writes outside txn fail when forbidden', async () => {
  const ir = await loadFlow('examples/flows/write_outside_txn.tf');
  const verdict = checkTransactions(ir, catalog, { forbidWritesOutsideTxn: true });
  assert.equal(verdict.ok, false);
  assert(verdict.reasons.some(r => r.includes('outside transaction')));
});
