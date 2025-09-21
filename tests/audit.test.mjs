import { test } from 'node:test';
import assert from 'node:assert/strict';
import { readFile, unlink, access, writeFile } from 'node:fs/promises';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { execFile } from 'node:child_process';
import { promisify } from 'node:util';

const execFileAsync = promisify(execFile);

const __dirname = path.dirname(fileURLToPath(import.meta.url));
const ROOT = path.resolve(__dirname, '..');
const REPORT_PATH = path.join(ROOT, 'out/0.4/audit/report.json');

async function fileExists(targetPath) {
  try {
    await access(targetPath);
    return true;
  } catch (err) {
    return false;
  }
}

test('audit report is emitted deterministically', async () => {
  await execFileAsync(process.execPath, ['scripts/audit/run.mjs'], { cwd: ROOT });
  const first = await readFile(REPORT_PATH);
  const report = JSON.parse(first);
  assert.strictEqual(typeof report.ok, 'boolean');

  await execFileAsync(process.execPath, ['scripts/audit/run.mjs'], { cwd: ROOT });
  const second = await readFile(REPORT_PATH);
  assert.ok(first.equals(second));
});

test('determinism check flags CRLF content', async () => {
  const tempPath = path.join(ROOT, 'tests', 'tmp-crlf.json');
  await writeFile(tempPath, '{\r\n}\r\n');
  try {
    const { run: runDeterminism } = await import('../scripts/audit/check-determinism.mjs');
    const result = await runDeterminism();
    const hit = result.issues.find((issue) => issue.path === 'tests/tmp-crlf.json' && issue.issue === 'has_crlf');
    assert.ok(hit, 'expected CRLF issue to be reported');
  } finally {
    if (await fileExists(tempPath)) {
      await unlink(tempPath);
    }
  }
});
