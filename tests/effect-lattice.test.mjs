import test from 'node:test';
import assert from 'node:assert/strict';
import { readFile } from 'node:fs/promises';
import { effectOf, canCommute, parSafe, EFFECT_FAMILIES } from '../packages/tf-l0-check/src/effect-lattice.mjs';
import { buildLatticeReport } from '../scripts/lattice-report.mjs';

const catalogRaw = await readFile('packages/tf-l0-spec/spec/catalog.json', 'utf8');
const catalog = JSON.parse(catalogRaw);

test('effectOf returns catalog effect for fully-qualified id', () => {
  assert.equal(effectOf('tf:information/hash@1', catalog), 'Pure');
});

test('effectOf returns catalog effect for bare primitive name', () => {
  assert.equal(effectOf('publish', catalog), 'Network.Out');
});

test('effectOf falls back to Network.Out heuristic for publish-like ids', () => {
  assert.equal(effectOf('acme/publish-event@1', catalog), 'Network.Out');
});

test('effectOf falls back to Crypto heuristic for sign-like ids', () => {
  assert.equal(effectOf('custom/sign-data@2', catalog), 'Crypto');
});

test('effectOf treats Pure specially even without catalog entry', () => {
  assert.equal(effectOf('Pure', catalog), 'Pure');
});

test('Pure commutes with Observability', () => {
  assert.equal(canCommute('Pure', 'Observability'), true);
});

test('Pure commutes with Storage.Write', () => {
  assert.equal(canCommute('Pure', 'Storage.Write'), true);
});

test('Pure commutes with Network.Out', () => {
  assert.equal(canCommute('Pure', 'Network.Out'), true);
});

test('Pure commutes with Crypto', () => {
  assert.equal(canCommute('Pure', 'Crypto'), true);
});

test('Pure commutes with Policy', () => {
  assert.equal(canCommute('Pure', 'Policy'), true);
});

test('Observability commutes with itself', () => {
  assert.equal(canCommute('Observability', 'Observability'), true);
});

test('Observability does not commute with Storage.Write', () => {
  assert.equal(canCommute('Observability', 'Storage.Write'), false);
});

test('Observability does not commute with Network.Out', () => {
  assert.equal(canCommute('Observability', 'Network.Out'), false);
});

test('Network.Out commutes with Observability', () => {
  assert.equal(canCommute('Network.Out', 'Observability'), true);
});

test('Network.Out does not commute with Storage.Write', () => {
  assert.equal(canCommute('Network.Out', 'Storage.Write'), false);
});

test('Storage.Write does not commute with itself without proofs', () => {
  assert.equal(canCommute('Storage.Write', 'Storage.Write'), false);
});

test('parSafe flags conflicting writes in parallel', () => {
  const writes = [{ uri: 'res://bucket/key', mode: 'write' }];
  assert.equal(parSafe('Storage.Write', 'Storage.Write', { writesA: writes, writesB: writes }), false);
});

test('parSafe accepts disjoint writes when provided', () => {
  const writesA = [{ uri: 'res://bucket/a', mode: 'write' }];
  const writesB = [{ uri: 'res://bucket/b', mode: 'write' }];
  const disjoint = (a, b) => a !== b;
  assert.equal(parSafe('Storage.Write', 'Storage.Write', { writesA, writesB, disjoint }), true);
});

test('parSafe defaults to safe for non-write effects', () => {
  assert.equal(parSafe('Observability', 'Network.Out'), true);
});

test('lattice report is deterministic and contains expected entries', () => {
  const first = buildLatticeReport();
  const second = buildLatticeReport({ families: EFFECT_FAMILIES });
  assert.deepEqual(first, second);
  assert.equal(first.commute.Pure.Observability, true);
  assert.equal(first.parSafe['Storage.Write']['Storage.Write'], false);
});
