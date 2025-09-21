#!/usr/bin/env node
import { writeFile, mkdir } from 'node:fs/promises';
import { dirname, join } from 'node:path';
import { fileURLToPath } from 'node:url';

import { EFFECT_FAMILIES, canCommute, parSafe } from '../packages/tf-l0-check/src/effect-lattice.mjs';

const here = dirname(fileURLToPath(import.meta.url));
const root = join(here, '..');
const outputPath = join(root, 'out/0.4/check/lattice-report.json');

const commute = {};
for (const a of EFFECT_FAMILIES) {
  commute[a] = {};
  for (const b of EFFECT_FAMILIES) {
    commute[a][b] = canCommute(a, b);
  }
}

const parMatrix = {};
for (const a of EFFECT_FAMILIES) {
  parMatrix[a] = {};
  for (const b of EFFECT_FAMILIES) {
    parMatrix[a][b] = parSafe(a, b);
  }
}

const report = {
  commute,
  parSafe: parMatrix
};

await mkdir(dirname(outputPath), { recursive: true });
await writeFile(outputPath, JSON.stringify(report, null, 2) + '\n');
