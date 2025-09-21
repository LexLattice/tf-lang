import test from 'node:test';
import assert from 'node:assert/strict';
import { readFile } from 'node:fs/promises';
import { dirname, join } from 'node:path';
import { fileURLToPath } from 'node:url';
import { execFile } from 'node:child_process';
import { promisify } from 'node:util';

import {
  EFFECT_FAMILIES,
  canCommute,
  effectOf,
  parSafe
} from '../packages/tf-l0-check/src/effect-lattice.mjs';

const exec = promisify(execFile);
const here = dirname(fileURLToPath(import.meta.url));
const root = join(here, '..');
const catalogPath = join(root, 'packages/tf-l0-spec/spec/catalog.json');
const reportPath = join(root, 'out/0.4/check/lattice-report.json');

async function loadCatalog() {
  const raw = await readFile(catalogPath, 'utf8');
  return JSON.parse(raw);
}

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

test('Pure commutes with UI', () => {
  assert.equal(canCommute('Pure', 'UI'), true);
});

test('Observability commutes with Pure', () => {
  assert.equal(canCommute('Observability', 'Pure'), true);
});

test('Observability commutes with Observability', () => {
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

test('Par Observability with Network.Out is safe', () => {
  assert.equal(parSafe('Observability', 'Network.Out'), true);
});

test('Par Storage.Write pair without writes is unsafe', () => {
  assert.equal(parSafe('Storage.Write', 'Storage.Write'), false);
});

test('Par Storage.Write pair with conflicting writes is unsafe', () => {
  const writes = [{ uri: 'res://bucket/a', mode: 'write' }];
  assert.equal(
    parSafe('Storage.Write', 'Storage.Write', { writesA: writes, writesB: writes }),
    false
  );
});

test('Par Storage.Write pair proven disjoint is safe', () => {
  const writesA = [{ uri: 'res://bucket/a', mode: 'write' }];
  const writesB = [{ uri: 'res://bucket/a', mode: 'write' }];
  assert.equal(
    parSafe('Storage.Write', 'Storage.Write', {
      writesA,
      writesB,
      disjoint: () => true
    }),
    true
  );
});

test('effectOf resolves via catalog and fallback', async () => {
  const catalog = await loadCatalog();
  assert.equal(effectOf('tf:network/publish@1', catalog), 'Network.Out');
  assert.equal(effectOf('notify-user'), 'Network.Out');
});

test('lattice report families cover known list', () => {
  assert.deepEqual(
    EFFECT_FAMILIES,
    [
      'Pure',
      'Observability',
      'Storage.Read',
      'Storage.Write',
      'Network.In',
      'Network.Out',
      'Crypto',
      'Policy',
      'Infra',
      'Time',
      'UI'
    ]
  );
});

test('lattice report is deterministic', async () => {
  await exec('node', ['scripts/lattice-report.mjs']);
  const first = await readFile(reportPath, 'utf8');
  await exec('node', ['scripts/lattice-report.mjs']);
  const second = await readFile(reportPath, 'utf8');
  assert.equal(first, second);
});
