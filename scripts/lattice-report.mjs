#!/usr/bin/env node
import { mkdir, writeFile } from 'node:fs/promises';
import path from 'node:path';
import { pathToFileURL } from 'node:url';
import {
  EFFECT_FAMILIES,
  canCommute,
  parSafe
} from '../packages/tf-l0-check/src/effect-lattice.mjs';

export function buildLatticeReport() {
  const commute = {};
  const par = {};
  for (const famA of EFFECT_FAMILIES) {
    commute[famA] = {};
    par[famA] = {};
    for (const famB of EFFECT_FAMILIES) {
      commute[famA][famB] = canCommute(famA, famB);
      par[famA][famB] = parSafe(famA, famB);
    }
  }
  return { commute, parSafe: par };
}

async function main() {
  const outDir = 'out/0.4/check';
  await mkdir(outDir, { recursive: true });
  const report = buildLatticeReport();
  await writeFile(
    path.join(outDir, 'lattice-report.json'),
    JSON.stringify(report, null, 2) + '\n',
    'utf8'
  );
}

if (process.argv[1] && import.meta.url === pathToFileURL(path.resolve(process.argv[1])).href) {
  await main();
}
