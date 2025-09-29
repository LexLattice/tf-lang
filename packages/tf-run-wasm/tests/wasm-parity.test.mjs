/*
 @tf-test
 kind: runtime
 speed: fast
 deps: node
 */

import assert from 'node:assert/strict';
import test from 'node:test';
import { mkdtemp, readFile, rm } from 'node:fs/promises';
import { tmpdir } from 'node:os';
import { join } from 'node:path';

import { run } from '../dist/index.js';

test('WASM and native evaluators stay in parity', async () => {
  const dir = await mkdtemp(join(tmpdir(), 'tf-run-wasm-'));
  try {
    const ir = {
      primitives: [
        { prim_id: 'tf:pure/identity@1', effect: 'return identity' },
        { prim: 'tf:resource/write-object@1' },
        'tf:integration/publish-topic@1',
      ],
    };
    const irSource = JSON.stringify(ir);

    const wasm = await run({ irSource });
    const native = await run({ irSource, disableWasm: true, statusPath: join(dir, 'status.json'), tracePath: join(dir, 'trace.jsonl') });

    assert.deepEqual(wasm, native);

    const statusRaw = await readFile(join(dir, 'status.json'), 'utf8');
    assert.ok(statusRaw.endsWith('\n'));
    assert.deepEqual(JSON.parse(statusRaw), native.status);

    const traceRaw = await readFile(join(dir, 'trace.jsonl'), 'utf8');
    assert.ok(traceRaw.endsWith('\n'));
    const traceLines = traceRaw
      .trim()
      .split('\n')
      .filter((line) => line.length > 0)
      .map((line) => JSON.parse(line));
    assert.deepEqual(traceLines, native.trace);
  } finally {
    await rm(dir, { recursive: true, force: true });
  }
});
