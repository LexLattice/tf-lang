import assert from 'node:assert/strict';
import { readFile, stat } from 'node:fs/promises';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import test from 'node:test';

import { generateCatalogDoc } from '../scripts/docgen/catalog.mjs';
import { generateDSLDoc } from '../scripts/docgen/dsl.mjs';
import { generateEffectsDoc } from '../scripts/docgen/effects.mjs';

const __filename = fileURLToPath(import.meta.url);
const __dirname = path.dirname(__filename);
const repoRoot = path.resolve(__dirname, '..');

function ensureSingleTrailingNewline(content) {
  assert.ok(content.endsWith('\n'), 'output should end with a newline');
  assert.ok(!content.endsWith('\n\n'), 'output should end with a single newline');
}

test('doc generators are deterministic', async (t) => {
  const catalogPath = await generateCatalogDoc({ root: repoRoot });
  const catalogContent = await readFile(catalogPath, 'utf8');
  ensureSingleTrailingNewline(catalogContent);
  const trimmed = catalogContent.trimEnd();
  const countLine = trimmed.split('\n').find(line => line.startsWith('Primitives: '));
  assert.ok(countLine, 'catalog doc should report primitive count');

  const catalogJson = JSON.parse(await readFile(path.join(repoRoot, 'packages', 'tf-l0-spec', 'spec', 'catalog.json'), 'utf8'));
  const expectedCount = Array.isArray(catalogJson?.primitives) ? catalogJson.primitives.length : 0;
  assert.strictEqual(countLine, `Primitives: ${expectedCount}`);

  await generateCatalogDoc({ root: repoRoot });
  const catalogContentAgain = await readFile(catalogPath, 'utf8');
  assert.strictEqual(catalogContentAgain, catalogContent);

  const dslPath = await generateDSLDoc({ root: repoRoot });
  await stat(dslPath);
  const dslContent = await readFile(dslPath, 'utf8');
  ensureSingleTrailingNewline(dslContent);
  await generateDSLDoc({ root: repoRoot });
  const dslContentAgain = await readFile(dslPath, 'utf8');
  assert.strictEqual(dslContentAgain, dslContent);

  const effectsPath = await generateEffectsDoc({ root: repoRoot });
  await stat(effectsPath);
  const effectsContent = await readFile(effectsPath, 'utf8');
  ensureSingleTrailingNewline(effectsContent);
  await generateEffectsDoc({ root: repoRoot });
  const effectsContentAgain = await readFile(effectsPath, 'utf8');
  assert.strictEqual(effectsContentAgain, effectsContent);
});
