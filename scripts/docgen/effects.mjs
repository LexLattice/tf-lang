#!/usr/bin/env node
import { writeFile } from 'node:fs/promises';
import path from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';

import {
  CANONICAL_EFFECT_FAMILIES,
  EFFECT_PRECEDENCE,
  canCommute,
  parSafe
} from '../../packages/tf-l0-check/src/effect-lattice.mjs';

function repoRoot() {
  const here = fileURLToPath(new URL('.', import.meta.url));
  return path.resolve(here, '..', '..');
}

function renderMatrix(families, fn) {
  const header = ['| Family |', ...families.map(f => ` \`${f}\` |`)].join('');
  const divider = ['| --- |', ...families.map(() => ' --- |')].join('');
  const rows = families.map(row => {
    const cells = families.map(col => (fn(row, col) ? '✅' : '❌'));
    return ['|', ` \`${row}\` |`, ...cells.map(cell => ` ${cell} |`)].join('');
  });
  return [header, divider, ...rows];
}

async function main() {
  const families = [...CANONICAL_EFFECT_FAMILIES];
  const precedence = [...EFFECT_PRECEDENCE];

  const lines = [];
  lines.push('# L0 Effects (generated)');
  lines.push('');

  lines.push('## Canonical families');
  for (const family of families) {
    lines.push(`- \`${family}\``);
  }
  lines.push('');

  lines.push('## Precedence order');
  lines.push(`- ${precedence.join(' > ')}`);
  lines.push('');

  lines.push('## Commutation matrix');
  lines.push(...renderMatrix(families, canCommute));
  lines.push('');

  lines.push('## Parallel safety matrix');
  lines.push(...renderMatrix(families, parSafe));
  lines.push('');

  const outPath = path.join(repoRoot(), 'docs', 'l0-effects.md');
  const payload = lines.join('\n');
  await writeFile(outPath, payload.endsWith('\n') ? payload : `${payload}\n`, 'utf8');
}

if (process.argv[1] && import.meta.url === pathToFileURL(path.resolve(process.argv[1])).href) {
  await main();
}

