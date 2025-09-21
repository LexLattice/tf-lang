import test from 'node:test';
import assert from 'node:assert/strict';
import { promisify } from 'node:util';
import { execFile as execFileCb } from 'node:child_process';
import { readFile } from 'node:fs/promises';
import path from 'node:path';
import { fileURLToPath } from 'node:url';

const execFile = promisify(execFileCb);
const repoRoot = path.resolve(fileURLToPath(new URL('..', import.meta.url)));

const scripts = [
  'scripts/docgen/catalog.mjs',
  'scripts/docgen/dsl.mjs',
  'scripts/docgen/effects.mjs'
].map(rel => path.join(repoRoot, rel));

const docs = [
  path.join(repoRoot, 'docs', 'l0-catalog.md'),
  path.join(repoRoot, 'docs', 'l0-dsl.md'),
  path.join(repoRoot, 'docs', 'l0-effects.md')
];

async function runDocgen() {
  for (const script of scripts) {
    await execFile('node', [script], { cwd: repoRoot });
  }
}

test('docgen outputs are deterministic', async () => {
  await runDocgen();

  const firstPass = new Map();
  for (const docPath of docs) {
    const content = await readFile(docPath, 'utf8');
    assert.ok(content.length > 0, `${docPath} should exist`);
    assert.ok(content.endsWith('\n'), `${docPath} should end with a newline`);
    assert.ok(!content.endsWith('\n\n'), `${docPath} should end with a single newline`);
    firstPass.set(docPath, content);
  }

  const catalogSrc = await readFile(path.join(repoRoot, 'packages', 'tf-l0-spec', 'spec', 'catalog.json'), 'utf8');
  const catalog = JSON.parse(catalogSrc);
  const primCount = Array.isArray(catalog?.primitives) ? catalog.primitives.length : 0;
  const catalogDoc = firstPass.get(path.join(repoRoot, 'docs', 'l0-catalog.md'));
  assert.ok(catalogDoc.includes(`Primitives: ${primCount}`));

  await runDocgen();

  for (const docPath of docs) {
    const next = await readFile(docPath, 'utf8');
    assert.strictEqual(next, firstPass.get(docPath));
  }
});

