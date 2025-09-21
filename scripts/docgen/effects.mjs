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

const __dirname = path.dirname(fileURLToPath(import.meta.url));
const repoRoot = path.resolve(__dirname, '..', '..');
const OUTPUT_PATH = path.join(repoRoot, 'docs', 'l0-effects.md');

function formatBoolean(value) {
  return value ? '✅' : '❌';
}

function buildMatrixRows(evaluator) {
  const header = ['Family', ...CANONICAL_EFFECT_FAMILIES];
  const rows = [header.join(' | '), header.map(() => '---').join(' | ')];
  for (const rowFam of CANONICAL_EFFECT_FAMILIES) {
    const cells = [rowFam];
    for (const colFam of CANONICAL_EFFECT_FAMILIES) {
      cells.push(formatBoolean(evaluator(rowFam, colFam)));
    }
    rows.push(cells.join(' | '));
  }
  return rows;
}

function buildEffectsMarkdown() {
  const lines = ['# L0 Effects (generated)'];

  lines.push('');
  lines.push('## Canonical families');
  for (const family of CANONICAL_EFFECT_FAMILIES) {
    lines.push(`* ${family}`);
  }

  lines.push('');
  lines.push('## Commutation matrix');
  lines.push(...buildMatrixRows((a, b) => canCommute(a, b)));

  lines.push('');
  lines.push('## Parallel safety matrix');
  lines.push(...buildMatrixRows((a, b) => parSafe(a, b)));

  lines.push('');
  lines.push('## Normalization precedence');
  EFFECT_PRECEDENCE.forEach((family, index) => {
    lines.push(`${index + 1}. ${family}`);
  });

  let doc = lines.join('\n');
  if (!doc.endsWith('\n')) {
    doc += '\n';
  }
  return doc;
}

export async function generateEffectsDoc({ outputPath = OUTPUT_PATH } = {}) {
  const markdown = buildEffectsMarkdown();
  await writeFile(outputPath, markdown, 'utf8');
  return markdown;
}

async function main() {
  await generateEffectsDoc();
}

if (process.argv[1] && import.meta.url === pathToFileURL(path.resolve(process.argv[1])).href) {
  await main();
}
