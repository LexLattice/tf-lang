import test from 'node:test';
import assert from 'node:assert/strict';
import { mkdtemp, writeFile } from 'node:fs/promises';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { execFile } from 'node:child_process';
import { promisify } from 'node:util';
import { fileURLToPath } from 'node:url';

const run = promisify(execFile);
const repoRoot = fileURLToPath(new URL('..', import.meta.url));

function cli(...args) {
  return run(process.execPath, ['packages/tf-compose/bin/tf.mjs', ...args], { cwd: repoRoot });
}

test('show prints a readable tree', async () => {
  const dir = await mkdtemp(join(tmpdir(), 'dsl-show-'));
  const file = join(dir, 'flow.tf');
  const src = 'seq{ write-object(uri="res://kv/x", key="a"); write-object(uri="res://kv/x", key="b") }';
  await writeFile(file, src, 'utf8');
  const { stdout } = await cli('show', file);
  const lines = stdout.trim().split('\n');
  assert.ok(lines[0].startsWith('Seq'));
  assert.ok(lines[1].startsWith('  Prim: write-object {key:"a", uri:"res://kv/x"}'));
  assert.ok(lines[2].startsWith('  Prim: write-object {key:"b", uri:"res://kv/x"}'));
});
