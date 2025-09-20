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

test('fmt produces canonical formatting and is idempotent', async () => {
  const dir = await mkdtemp(join(tmpdir(), 'dsl-fmt-'));
  const file = join(dir, 'flow.tf');
  const messy = 'seq{write-object( key ="b",uri="res://kv/x", meta={ retry:{ count:2, }, }, list=[true,false,], value=-3.5 );par{ hash ; write-object( uri="res://kv/x",key="a") }}';
  await writeFile(file, messy, 'utf8');

  const { stdout } = await execFileAsync(process.execPath, [CLI, 'fmt', file]);
  const expected = [
    'seq{',
    '  write-object(key="b", list=[true, false], meta={retry:{count:2}}, uri="res://kv/x", value=-3.5);',
    '  par{',
    '    hash;',
    '    write-object(key="a", uri="res://kv/x")',
    '  }',
    '}'
  ].join('\n');
  assert.equal(stdout, expected + '\n');

  await writeFile(file, stdout, 'utf8');
  const second = await execFileAsync(process.execPath, [CLI, 'fmt', file]);
  assert.equal(second.stdout, stdout);
});
