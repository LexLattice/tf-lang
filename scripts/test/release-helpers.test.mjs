// @tf-test kind: node, speed: fast, deps: node
import test from 'node:test';
import assert from 'node:assert/strict';
import { mkdtemp, rm, readFile } from 'node:fs/promises';
import { tmpdir } from 'node:os';
import path from 'node:path';

import { emitJson, parseArgs, UsageError } from '../../tools/release/_shared.mjs';

test('parseArgs parses boolean and value flags', () => {
  const result = parseArgs(['--out', 'out/status.json', '--verbose'], {
    usage: 'cli [options]',
    flags: {
      out: { description: 'path', required: true },
      verbose: { description: 'verbose' },
    },
  });
  assert.equal(result.out, 'out/status.json');
  assert.equal(result.verbose, true);
  assert.equal(result.help, false);
  assert.ok(result.helpText.includes('Usage: cli [options]'));
});

test('parseArgs throws UsageError on unknown flag', () => {
  assert.throws(
    () => {
      parseArgs(['--unknown'], {
        usage: 'cli [options]',
      });
    },
    (error) => error instanceof UsageError && error.exitCode === 2,
  );
});

test('emitJson writes optional file and returns body', async () => {
  const dir = await mkdtemp(path.join(tmpdir(), 'release-helpers-test-'));
  const target = path.join(dir, 'status.json');
  try {
    const body = await emitJson({ ok: true }, target);
    assert.equal(body, '{\n  "ok": true\n}\n');
    const onDisk = await readFile(target, 'utf8');
    assert.equal(onDisk, body);
  } finally {
    await rm(dir, { recursive: true, force: true });
  }
});
