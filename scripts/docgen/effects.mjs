#!/usr/bin/env node
import path from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';

import {
  CANONICAL_EFFECT_FAMILIES,
  EFFECT_PRECEDENCE,
  canCommute,
  parSafe
} from '../../packages/tf-l0-check/src/effect-lattice.mjs';
import { getFixtureSeed, resolveRepoRoot, writeDoc } from './utils.mjs';

const SCRIPT_NAME = 'scripts/docgen/effects.mjs';

const __filename = fileURLToPath(import.meta.url);
const __dirname = path.dirname(__filename);

getFixtureSeed();

function boolCell(value) {
  return value ? '✅' : '❌';
}

function renderMatrix(title, families, compute) {
  const lines = [];
  lines.push(`## ${title}`);
  lines.push('');
  const header = ['Prev \\ Next', ...families];
  lines.push(`| ${header.join(' | ')} |`);
  lines.push(`| ${header.map(() => '---').join(' | ')} |`);
  for (const prev of families) {
    const row = [prev];
    for (const next of families) {
      row.push(boolCell(compute(prev, next)));
    }
    lines.push(`| ${row.join(' | ')} |`);
  }
  lines.push('');
  return lines;
}

export async function generateEffectsDoc(options = {}) {
  const repoRoot = resolveRepoRoot(__dirname, options.root);
  const outPath = path.join(repoRoot, 'docs', 'l0-effects.md');
  const families = CANONICAL_EFFECT_FAMILIES.slice();
  const precedence = EFFECT_PRECEDENCE.slice();

  const lines = [];
  lines.push('# L0 Effects Lattice (generated)');
  lines.push('');
  lines.push('## Canonical families');
  lines.push('');
  for (const family of families) {
    lines.push(`- ${family}`);
  }
  lines.push('');

  lines.push(...renderMatrix('Commutation matrix', families, (prev, next) => canCommute(prev, next)));
  lines.push(...renderMatrix('Parallel safety matrix', families, (prev, next) => parSafe(prev, next)));

  lines.push('## Precedence order');
  lines.push('');
  lines.push('The normalize pass orders effects using the following precedence:');
  lines.push('');
  let index = 1;
  for (const family of precedence) {
    lines.push(`${index}. ${family}`);
    index += 1;
  }
  lines.push('');

  await writeDoc(outPath, SCRIPT_NAME, lines);
  return outPath;
}

if (process.argv[1] && import.meta.url === pathToFileURL(path.resolve(process.argv[1])).href) {
  await generateEffectsDoc();
}
