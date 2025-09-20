import test from 'node:test';
import assert from 'node:assert/strict';
import { mkdtemp, writeFile, readFile } from 'node:fs/promises';
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

test('fmt normalizes and sorts arguments', async () => {
  const dir = await mkdtemp(join(tmpdir(), 'dsl-fmt-'));
  const file = join(dir, 'flow.tf');
  const messy = 'seq{write-object(flag=true ,uri="res://kv/a", key="x", arr=[1,2,], meta={retry:{count:2,}}, note=fast);write-object(key="y",uri="res://kv/a") }';
  await writeFile(file, messy, 'utf8');
  const { stdout } = await cli('fmt', file);
  const expected = `seq{\n  write-object(arr=[1, 2], flag=true, key="x", meta={retry:{count:2}}, note="fast", uri="res://kv/a");\n  write-object(key="y", uri="res://kv/a")\n}\n`;
  assert.equal(stdout, expected);
});

test('fmt is idempotent with --write', async () => {
  const dir = await mkdtemp(join(tmpdir(), 'dsl-fmt-idem-'));
  const file = join(dir, 'flow.tf');
  const messy = 'seq{write-object(key="x", uri="res://kv/a" )}';
  await writeFile(file, messy, 'utf8');
  await cli('fmt', file, '--write');
  const once = await readFile(file, 'utf8');
  await cli('fmt', file, '-w');
  const twice = await readFile(file, 'utf8');
  assert.equal(once, twice);
});
