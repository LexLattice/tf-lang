// @tf-test kind=infra area=audit speed=fast deps=node

import { test } from 'node:test';
import assert from 'node:assert/strict';
import { readFile, unlink, access, writeFile, mkdir } from 'node:fs/promises';
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

async function runAudit() {
  try {
    await execFileAsync(process.execPath, ['scripts/audit/run.mjs'], { cwd: ROOT });
  } catch (err) {
    if (err?.code !== 1) {
      throw err;
    }
  }
}

test('audit report is emitted deterministically', async () => {
  await runAudit();
  const first = await readFile(REPORT_PATH);
  const report = JSON.parse(first);
  assert.strictEqual(typeof report.ok, 'boolean');

  await runAudit();
  const second = await readFile(REPORT_PATH);
  assert.ok(first.equals(second));
});

test('determinism check flags CRLF content', async () => {
  const tempDir = path.join(ROOT, 'tmp');
  const tempPath = path.join(tempDir, 'audit-crlf.json');
  await mkdir(tempDir, { recursive: true });
  await writeFile(tempPath, '{\r\n}\r\n');
  try {
    const { run: runDeterminism } = await import('../scripts/audit/check-determinism.mjs');
    const result = await runDeterminism();
    const hit = result.issues.find((issue) => issue.path === 'tmp/audit-crlf.json' && issue.issue === 'has_crlf');
    assert.ok(hit, 'expected CRLF issue to be reported');
  } finally {
    if (await fileExists(tempPath)) {
      await unlink(tempPath);
    }
  }
});
