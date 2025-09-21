import { test } from 'node:test';
import assert from 'node:assert/strict';
import { promisify } from 'node:util';
import { execFile } from 'node:child_process';
import { readFile } from 'node:fs/promises';
import path from 'node:path';
import { fileURLToPath } from 'node:url';

const execFileAsync = promisify(execFile);
const __dirname = path.dirname(fileURLToPath(import.meta.url));
const ROOT = path.resolve(__dirname, '..');

const DOC_SCRIPTS = [
  { script: 'catalog.mjs', output: 'docs/l0-catalog.md' },
  { script: 'dsl.mjs', output: 'docs/l0-dsl.md' },
  { script: 'effects.mjs', output: 'docs/l0-effects.md' }
];

async function runScript(name) {
  const scriptPath = path.join(ROOT, 'scripts/docgen', name);
  await execFileAsync('node', [scriptPath], { cwd: ROOT });
}

test('docgen outputs are deterministic', async () => {
  for (const entry of DOC_SCRIPTS) {
    await runScript(entry.script);
  }

  const snapshots = new Map();

  for (const entry of DOC_SCRIPTS) {
    const absPath = path.join(ROOT, entry.output);
    const content = await readFile(absPath, 'utf8');
    assert.ok(content.endsWith('\n'), `${entry.output} should end with a newline`);
    assert.ok(!content.endsWith('\n\n'), `${entry.output} should not end with an empty line`);
    snapshots.set(entry.output, content);
  }

  const catalogPath = path.join(ROOT, 'packages/tf-l0-spec/spec/catalog.json');
  const catalog = JSON.parse(await readFile(catalogPath, 'utf8'));
  const primitiveCount = Array.isArray(catalog?.primitives) ? catalog.primitives.length : 0;
  const catalogDoc = snapshots.get('docs/l0-catalog.md') ?? '';
  const countLine = catalogDoc.split('\n').find(line => line.startsWith('Primitives: '));
  assert.ok(countLine, 'catalog doc should include primitive count');
  assert.equal(countLine, `Primitives: ${primitiveCount}`);

  for (const entry of DOC_SCRIPTS) {
    await runScript(entry.script);
  }

  for (const entry of DOC_SCRIPTS) {
    const absPath = path.join(ROOT, entry.output);
    const next = await readFile(absPath, 'utf8');
    assert.equal(next, snapshots.get(entry.output));
  }
});
