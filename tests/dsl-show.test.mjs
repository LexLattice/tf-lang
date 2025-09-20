import test from 'node:test';
import assert from 'node:assert/strict';
import { mkdtemp, writeFile } from 'node:fs/promises';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { fileURLToPath } from 'node:url';
import { execFile } from 'node:child_process';
import { promisify } from 'node:util';

const execFileAsync = promisify(execFile);
const CLI = fileURLToPath(new URL('../packages/tf-compose/bin/tf.mjs', import.meta.url));

test('show renders tree view with ordered children', async () => {
  const dir = await mkdtemp(join(tmpdir(), 'dsl-show-'));
  const seqFile = join(dir, 'seq.tf');
  const seqSrc = 'seq{ write-object(uri="res://kv/x", key="a"); write-object(uri="res://kv/x", key="b") }';
  await writeFile(seqFile, seqSrc, 'utf8');

  const { stdout } = await execFileAsync(process.execPath, [CLI, 'show', seqFile]);
  const lines = stdout.trim().split('\n');
  assert.equal(lines[0], 'Seq');
  const first = lines.findIndex(line => line.includes('key:"a"'));
  const second = lines.findIndex(line => line.includes('key:"b"'));
  assert(first >= 0 && second >= 0);
  assert(first < second);

  const primFile = join(dir, 'prim.tf');
  await writeFile(primFile, 'hash', 'utf8');
  const { stdout: primOut } = await execFileAsync(process.execPath, [CLI, 'show', primFile]);
  assert.ok(primOut.trim().startsWith('Prim'));
});
