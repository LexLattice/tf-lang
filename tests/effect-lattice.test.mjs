import test from 'node:test';
import assert from 'node:assert/strict';
import { readFile } from 'node:fs/promises';
import {
  EFFECT_FAMILIES,
  effectOf,
  canCommute,
  parSafe
} from '../packages/tf-l0-check/src/effect-lattice.mjs';
import { buildLatticeReport } from '../scripts/lattice-report.mjs';
import { conflict } from '../packages/tf-l0-check/src/footprints.mjs';

const catalog = JSON.parse(
  await readFile('packages/tf-l0-spec/spec/catalog.json', 'utf8')
);

const emptyCatalog = { primitives: [] };

// Pure commutes with a sampling of families
const pureSamples = ['Observability', 'Storage.Write', 'Network.Out', 'Crypto', 'Policy', 'UI'];

for (const fam of pureSamples) {
  test(`Pure commutes with ${fam}`, () => {
    assert.equal(canCommute('Pure', fam), true);
  });
}

// Observability commutation cases
test('Observability commutes with Pure', () => {
  assert.equal(canCommute('Observability', 'Pure'), true);
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

// Network.Out commutation cases
test('Network.Out commutes with Observability', () => {
  assert.equal(canCommute('Network.Out', 'Observability'), true);
});

test('Network.Out commutes with Pure', () => {
  assert.equal(canCommute('Network.Out', 'Pure'), true);
});

test('Network.Out does not commute with Storage.Write', () => {
  assert.equal(canCommute('Network.Out', 'Storage.Write'), false);
});

// Parallel safety checks
const writeA = [{ uri: 'res://kv/a', mode: 'write' }];
const writeB = [{ uri: 'res://kv/b', mode: 'write' }];
const writeConflict = [{ uri: 'res://kv/shared', mode: 'write' }];

test('Parallel Storage.Write with overlap is unsafe', () => {
  assert.equal(
    parSafe('Storage.Write', 'Storage.Write', {
      conflict,
      writesA: writeConflict,
      writesB: writeConflict
    }),
    false
  );
});

test('Parallel Storage.Write with disjoint URIs is safe', () => {
  assert.equal(
    parSafe('Storage.Write', 'Storage.Write', {
      conflict,
      writesA: writeA,
      writesB: writeB
    }),
    true
  );
});

test('Parallel Observability and Network.Out is safe', () => {
  assert.equal(parSafe('Observability', 'Network.Out'), true);
});

// effectOf coverage
test('effectOf prefers catalog effects', () => {
  assert.equal(effectOf('tf:network/publish@1', catalog), 'Network.Out');
});

test('effectOf falls back to heuristics when missing', () => {
  assert.equal(effectOf('tf:resource/read-object@1', emptyCatalog), 'Storage.Read');
});

test('effectOf returns Pure when unknown', () => {
  assert.equal(effectOf('tf:unknown/thing@1', emptyCatalog), 'Pure');
});

// Lattice report determinism
test('Lattice report matrix is deterministic', () => {
  const first = buildLatticeReport();
  const second = buildLatticeReport();
  assert.deepEqual(first, second);
  // ensure matrix covers declared families
  for (const fam of EFFECT_FAMILIES) {
    assert.ok(fam in first.commute);
    assert.ok(fam in first.parSafe);
  }
});
