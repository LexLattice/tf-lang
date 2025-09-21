import test from 'node:test';
import assert from 'node:assert/strict';

const {
  effectOf,
  canCommute,
  parSafe
} = await import('../packages/tf-l0-check/src/effect-lattice.mjs');
const { run: runReport } = await import('../scripts/lattice-report.mjs');

const sampleCatalog = {
  primitives: [
    {
      id: 'tf:observability/emit-metric@1',
      name: 'emit-metric',
      effects: ['Observability']
    },
    {
      id: 'tf:storage/read-object@1',
      name: 'read-object',
      effects: ['Storage.Read']
    }
  ]
};

test('Pure commutes with Pure', () => {
  assert.equal(canCommute('Pure', 'Pure'), true);
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

test('Network.Out commutes with Pure', () => {
  assert.equal(canCommute('Network.Out', 'Pure'), true);
});

test('Network.Out commutes with Observability', () => {
  assert.equal(canCommute('Network.Out', 'Observability'), true);
});

test('Network.Out does not commute with Storage.Write', () => {
  assert.equal(canCommute('Network.Out', 'Storage.Write'), false);
});

test('Storage.Write does not commute with Storage.Write', () => {
  assert.equal(canCommute('Storage.Write', 'Storage.Write'), false);
});

test('Storage.Write does not commute with Crypto', () => {
  assert.equal(canCommute('Storage.Write', 'Crypto'), false);
});

test('effectOf prefers catalog entries', () => {
  assert.equal(effectOf('tf:observability/emit-metric@1', sampleCatalog), 'Observability');
});

test('effectOf falls back to regex heuristics', () => {
  assert.equal(effectOf('read-object', {}), 'Storage.Read');
});

test('parallel Storage.Write pair defaults to unsafe', () => {
  assert.equal(
    parSafe('Storage.Write', 'Storage.Write', {
      writesA: [{ uri: 'res://x', mode: 'write' }],
      writesB: [{ uri: 'res://x', mode: 'write' }]
    }),
    false
  );
});

test('parallel Storage.Write pair with disjoint proof is safe', () => {
  assert.equal(
    parSafe('Storage.Write', 'Storage.Write', {
      writesA: [{ uri: 'res://a', mode: 'write' }],
      writesB: [{ uri: 'res://b', mode: 'write' }],
      disjoint: (a, b) => a !== b
    }),
    true
  );
});

test('parallel Observability and Network.Out are safe', () => {
  assert.equal(parSafe('Observability', 'Network.Out'), true);
});

test('lattice report generation is deterministic', async () => {
  const first = await runReport();
  const second = await runReport();
  assert.deepEqual(first, second);
});
