#!/usr/bin/env node
import { mkdir, writeFile } from 'node:fs/promises';
import path from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';

import {
  CANONICAL_EFFECT_FAMILIES,
  EFFECT_PRECEDENCE,
  canCommute,
  parSafe
} from '../../packages/tf-l0-check/src/effect-lattice.mjs';

const __dirname = path.dirname(fileURLToPath(import.meta.url));
const ROOT = path.resolve(__dirname, '../..');
const OUT_PATH = path.join(ROOT, 'docs/l0-effects.md');

function ensureTrailingNewline(payload) {
  return payload.endsWith('\n') ? payload : `${payload}\n`;
}

function renderMatrix(title, headerLabel, evaluator) {
  const families = [...CANONICAL_EFFECT_FAMILIES];
  const header = ['| ' + headerLabel + ' |', ...families.map(f => ` ${formatFamily(f)} |`)].join('');
  const separator = ['| --- |', ...families.map(() => ' --- |')].join('');
  const rows = families.map(rowFamily => {
    const cells = families.map(colFamily => evaluator(rowFamily, colFamily) ? ' ✅ ' : ' ❌ ');
    return ['| ' + formatFamily(rowFamily) + ' |', ...cells.map(cell => cell + '|')].join('');
  });
  return [`## ${title}`, '', header, separator, ...rows, ''];
}

function formatFamily(family) {
  return `\`${family}\``;
}

async function buildDoc() {
  const lines = ['# L0 Effects (generated)', ''];

  lines.push('## Canonical Families');
  lines.push('');
  for (const family of CANONICAL_EFFECT_FAMILIES) {
    lines.push(`- ${formatFamily(family)}`);
  }
  lines.push('');

  lines.push(...renderMatrix('Commutation Matrix', 'Prev \\ Next', (a, b) => canCommute(a, b)));
  lines.push(...renderMatrix('Parallel Safety Matrix', 'Branch A \\ Branch B', (a, b) => parSafe(a, b)));

  lines.push('## Precedence');
  lines.push('');
  lines.push(`Normalization order: ${EFFECT_PRECEDENCE.map(formatFamily).join(' > ')}`);
  lines.push('');

  const payload = ensureTrailingNewline(lines.join('\n'));
  await mkdir(path.dirname(OUT_PATH), { recursive: true });
  await writeFile(OUT_PATH, payload, 'utf8');
}

if (process.argv[1] && import.meta.url === pathToFileURL(path.resolve(process.argv[1])).href) {
  await buildDoc();
}

export { buildDoc };
