import { mkdir, writeFile } from 'node:fs/promises';
import { dirname, join } from 'node:path';
import { pathToFileURL } from 'node:url';

import { canonicalize } from '../packages/tf-l0-spec/scripts/canonical-json.mjs';
import {
  EFFECT_FAMILIES,
  canCommute,
  parSafe
} from '../packages/tf-l0-check/src/effect-lattice.mjs';

const OUTPUT_PATH = join('out', '0.4', 'check', 'lattice-report.json');

function buildMatrix(families, fn) {
  const matrix = {};
  for (const a of families) {
    const row = {};
    for (const b of families) {
      row[b] = fn(a, b);
    }
    matrix[a] = row;
  }
  return matrix;
}

export async function run() {
  const families = EFFECT_FAMILIES;
  const commute = buildMatrix(families, canCommute);
  const parallel = buildMatrix(families, (a, b) => parSafe(a, b));

  const payload = {
    commute,
    parSafe: parallel
  };

  await mkdir(dirname(OUTPUT_PATH), { recursive: true });
  await writeFile(OUTPUT_PATH, canonicalize(payload) + '\n', 'utf8');
  return payload;
}

const entryHref = process.argv[1] ? pathToFileURL(process.argv[1]).href : undefined;
if (import.meta.url === entryHref) {
  await run();
}
