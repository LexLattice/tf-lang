/*
 @tf-test
 kind: runtime
 speed: fast
 deps: node
 */

import assert from 'node:assert/strict';
import test from 'node:test';
import { execFile } from 'node:child_process';
import { promisify } from 'node:util';
import { mkdtemp, writeFile, readFile, rm } from 'node:fs/promises';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { fileURLToPath } from 'node:url';

const execFileAsync = promisify(execFile);
const testDir = fileURLToPath(new URL('.', import.meta.url));
const packageRoot = join(testDir, '..');

const CLI_PATH = join(packageRoot, 'bin', 'run-wasm.mjs');

test('tf-run-wasm CLI emits deterministic JSON artifacts', async () => {
  const dir = await mkdtemp(join(tmpdir(), 'tf-run-wasm-cli-'));
  try {
    const flowPath = join(dir, 'flow.tf');
    await writeFile(
      flowPath,
      [
        '# synthetic flow used in tests',
        'tf:pure/identity@1 return identity',
        'tf:resource/write-object@1 persist payload',
      ].join('\n'),
      'utf8',
    );

    const outPath = join(dir, 'result.json');
    const statusPath = join(dir, 'status.json');
    const tracePath = join(dir, 'trace.jsonl');

    const { stdout } = await execFileAsync(process.execPath, [CLI_PATH, '--flow', flowPath, '--out', outPath, '--status', statusPath, '--trace', tracePath, '--json'], {
      cwd: packageRoot,
      maxBuffer: 2 * 1024 * 1024,
    });

    const stdoutBody = stdout.toString();
    assert.ok(stdoutBody.endsWith('\n'));
    const printed = JSON.parse(stdoutBody.trim());

    const storedRaw = await readFile(outPath, 'utf8');
    assert.ok(storedRaw.endsWith('\n'));
    const stored = JSON.parse(storedRaw);
    assert.deepEqual(printed, stored);

    const statusRaw = await readFile(statusPath, 'utf8');
    assert.ok(statusRaw.endsWith('\n'));
    assert.deepEqual(JSON.parse(statusRaw), printed.status);

    const traceRaw = await readFile(tracePath, 'utf8');
    assert.ok(traceRaw.endsWith('\n'));
    const traceLines = traceRaw
      .trim()
      .split('\n')
      .filter((line) => line.length > 0)
      .map((line) => JSON.parse(line));
    assert.deepEqual(traceLines, printed.trace);
  } finally {
    await rm(dir, { recursive: true, force: true });
  }
});
