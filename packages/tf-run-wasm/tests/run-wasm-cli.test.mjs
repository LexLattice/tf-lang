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
import { existsSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { fileURLToPath } from 'node:url';

const execFileAsync = promisify(execFile);
const testDir = fileURLToPath(new URL('.', import.meta.url));
const packageRoot = join(testDir, '..');

const CLI_PATH = join(packageRoot, 'bin', 'cli.mjs');
const DIST_ENTRY = join(packageRoot, 'dist', 'index.js');

let buildPromise;
async function ensureCliBuilt() {
  if (existsSync(DIST_ENTRY)) return;
  if (!buildPromise) {
    buildPromise = execFileAsync('pnpm', ['--filter', '@tf-lang/tf-run-wasm', 'run', 'build'], {
      cwd: packageRoot,
      maxBuffer: 2 * 1024 * 1024,
    }).catch((err) => {
      buildPromise = undefined;
      throw err;
    });
  }
  await buildPromise;
}

test('tf-run-wasm CLI writes normalized status and trace files', async () => {
  const dir = await mkdtemp(join(tmpdir(), 'tf-run-wasm-cli-'));
  try {
    const irPath = join(dir, 'sample.ir.json');
    const ir = {
      primitives: [
        { prim_id: 'tf:pure/identity@1', effect: 'identity' },
        { prim: 'tf:resource/write-object@1', effect: 'persist' },
        'tf:integration/publish-topic@1',
      ],
    };
    await writeFile(irPath, JSON.stringify(ir), 'utf8');

    const statusPath = join(dir, 'status.json');
    const tracePath = join(dir, 'trace.jsonl');

    await ensureCliBuilt();

    const { stdout, stderr } = await execFileAsync(
      process.execPath,
      [CLI_PATH, '--ir', irPath, '--status', statusPath, '--trace', tracePath],
      {
        cwd: packageRoot,
        maxBuffer: 2 * 1024 * 1024,
      },
    );

    const stdoutText = stdout.toString();
    assert.match(stdoutText, /^wrote status=true trace=true steps=\d+\n$/);
    assert.equal(stderr.toString(), '');

    const statusRaw = await readFile(statusPath, 'utf8');
    assert.ok(statusRaw.endsWith('\n'));
    const status = JSON.parse(statusRaw);
    assert.equal(status.ok, true);
    assert.ok(['tf-eval-wasm', 'tf-eval-stub'].includes(status.engine));
    assert.equal(status.bytes, Buffer.byteLength(JSON.stringify(ir), 'utf8'));

    const traceRaw = await readFile(tracePath, 'utf8');
    assert.ok(traceRaw.endsWith('\n'));
    const traceLines = traceRaw
      .trim()
      .split('\n')
      .filter((line) => line.length > 0)
      .map((line) => JSON.parse(line));
    assert.equal(traceLines.length, ir.primitives.length);
    for (const item of traceLines) {
      assert.ok(typeof item === 'object' && item !== null);
      assert.ok('prim_id' in item);
    }
  } finally {
    await rm(dir, { recursive: true, force: true });
  }
});
