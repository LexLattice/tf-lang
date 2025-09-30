import { test } from 'node:test';
import assert from 'node:assert/strict';
import path from 'node:path';
import fs from 'node:fs/promises';
import { execFile } from 'node:child_process';
import { promisify } from 'node:util';

const execFileAsync = promisify(execFile);

test('checker writes error reports to requested out path', async () => {
  const brokenPath = path.resolve('out/broken.l0.json');
  const outPath = path.resolve('out/tmp/error-report.json');

  await fs.mkdir(path.dirname(brokenPath), { recursive: true });
  await fs.writeFile(brokenPath, '{ not valid json');
  await fs.mkdir(path.dirname(outPath), { recursive: true });
  await fs.rm(outPath, { force: true });

  let caughtError;
  try {
    await execFileAsync('node', [
      'packages/checker/check.mjs',
      brokenPath,
      '--out',
      outPath,
    ]);
  } catch (error) {
    caughtError = error;
  }

  assert.ok(caughtError, 'expected checker to exit with failure');
  const content = await fs.readFile(outPath, 'utf8');
  const report = JSON.parse(content);
  assert.equal(report.status, 'RED');
  assert.equal(report.pipeline_id, null);
  assert.ok(typeof report.error === 'string' && report.error.length > 0);
});
