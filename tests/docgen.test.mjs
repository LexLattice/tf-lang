import test from 'node:test';
import assert from 'node:assert/strict';
import { readFile } from 'node:fs/promises';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { execFile } from 'node:child_process';
import { promisify } from 'node:util';

const execFileAsync = promisify(execFile);

const __dirname = path.dirname(fileURLToPath(import.meta.url));
const repoRoot = path.resolve(__dirname, '..');

const DOC_PATHS = {
  catalog: path.join(repoRoot, 'docs', 'l0-catalog.md'),
  dsl: path.join(repoRoot, 'docs', 'l0-dsl.md'),
  effects: path.join(repoRoot, 'docs', 'l0-effects.md')
};

const SCRIPT_PATHS = [
  path.join(repoRoot, 'scripts', 'docgen', 'catalog.mjs'),
  path.join(repoRoot, 'scripts', 'docgen', 'dsl.mjs'),
  path.join(repoRoot, 'scripts', 'docgen', 'effects.mjs')
];

async function runDocgenScripts() {
  for (const scriptPath of SCRIPT_PATHS) {
    await execFileAsync('node', [scriptPath], { cwd: repoRoot });
  }
}

async function loadDocs() {
  const entries = {};
  for (const [key, docPath] of Object.entries(DOC_PATHS)) {
    entries[key] = await readFile(docPath, 'utf8');
  }
  return entries;
}

function assertSingleTrailingNewline(content, label) {
  assert.ok(content.endsWith('\n'), `${label} should end with a newline`);
  assert.ok(!content.endsWith('\n\n'), `${label} should not end with extra blank lines`);
}

test('docgen outputs are deterministic and aligned with catalog', async () => {
  await runDocgenScripts();
  const firstDocs = await loadDocs();

  for (const [key, content] of Object.entries(firstDocs)) {
    assertSingleTrailingNewline(content, key);
  }

  const catalogJsonPath = path.join(repoRoot, 'packages', 'tf-l0-spec', 'spec', 'catalog.json');
  const catalogJson = JSON.parse(await readFile(catalogJsonPath, 'utf8'));
  const primitiveCount = Array.isArray(catalogJson?.primitives) ? catalogJson.primitives.length : 0;

  const countMatch = firstDocs.catalog.match(/^Primitives: (\d+)/m);
  assert.ok(countMatch, 'catalog doc should include primitive count line');
  const countValue = Number(countMatch[1]);
  if (primitiveCount > 0) {
    assert.equal(countValue, primitiveCount, 'primitive count line should match catalog length');
  } else {
    assert.equal(countValue, 0, 'primitive count should be zero when catalog is empty');
  }

  await runDocgenScripts();
  const secondDocs = await loadDocs();

  for (const key of Object.keys(DOC_PATHS)) {
    assert.equal(secondDocs[key], firstDocs[key], `${key} doc changed after re-running docgen`);
  }
});
