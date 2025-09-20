import test from 'node:test';
import assert from 'node:assert/strict';
import { readFile } from 'node:fs/promises';

const { parseDSL } = await import('../packages/tf-compose/src/parser.mjs');
const { emitSMT } = await import('../packages/tf-l0-proofs/src/smt.mjs');
const { checkIR } = await import('../packages/tf-l0-check/src/check.mjs');

async function loadCatalog() {
  try {
    const catalogUrl = new URL('../packages/tf-l0-spec/spec/catalog.json', import.meta.url);
    return JSON.parse(await readFile(catalogUrl, 'utf8'));
  } catch {
    return { primitives: [] };
  }
}

function annotateWrites(node, catalog) {
  if (!node || typeof node !== 'object' || node === null) {
    return;
  }
  const verdict = checkIR(node, catalog) || {};
  node.writes = Array.isArray(verdict.writes) ? verdict.writes : [];
  if (Array.isArray(node.children)) {
    for (const child of node.children) {
      annotateWrites(child, catalog);
    }
  }
}

function countPairs(node) {
  if (!node || typeof node !== 'object' || node === null) {
    return 0;
  }
  let total = 0;
  if (node.node === 'Par' && Array.isArray(node.children)) {
    const n = node.children.length;
    total += (n * (n - 1)) / 2;
  }
  if (Array.isArray(node.children)) {
    for (const child of node.children) {
      total += countPairs(child);
    }
  }
  return total;
}

test('storage conflict flow encodes at least one conflict pair', async () => {
  const catalog = await loadCatalog();
  const src = await readFile(new URL('../examples/flows/storage_conflict.tf', import.meta.url), 'utf8');
  const ir = parseDSL(src);
  annotateWrites(ir, catalog);
  const smt = emitSMT(ir);
  assert.match(smt, /\(declare-const conflict_\d+_\d+_\d+ Bool\)/);
  assert.match(smt, /\(assert \(not \(or conflict_\d+_\d+_\d+/);
  const equality = smt.match(/\(assert \(= (conflict_\d+_\d+_\d+) \(= "([^"]+)" "([^"]+)"\)\)\)/);
  assert.ok(equality, 'expected an equality assertion for a conflict variable');
  assert.equal(equality[2], equality[3]);
  assert.match(smt, /\(check-sat\)/);
});

test('storage ok flow is deterministic and pair counts match', async () => {
  const catalog = await loadCatalog();
  const src = await readFile(new URL('../examples/flows/storage_ok.tf', import.meta.url), 'utf8');
  const ir = parseDSL(src);
  annotateWrites(ir, catalog);
  const smtOne = emitSMT(ir);
  const smtTwo = emitSMT(ir);
  assert.equal(smtOne, smtTwo);
  const expectedPairs = countPairs(ir);
  const declared = (smtOne.match(/\(declare-const conflict_/g) || []).length;
  assert.equal(declared, expectedPairs);
  assert.match(smtOne, /\(assert \(not \(or conflict_\d+_\d+_\d+/);
  assert.match(smtOne, /\(check-sat\)/);
});
