// @tf-test kind=product area=trace speed=fast deps=node
import { mkdtemp, readFile, writeFile } from 'node:fs/promises';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { fileURLToPath } from 'node:url';
import assert from 'node:assert/strict';
import { test } from 'node:test';
import { spawn } from 'node:child_process';

import { validateTraceRecord } from '../dist/lib/validate.js';
import { ingestTraceFile } from '../dist/lib/ingest.js';

const packageRoot = fileURLToPath(new URL('..', import.meta.url));

async function withTempDir(fn) {
  const dir = await mkdtemp(join(tmpdir(), 'tf-trace-'));
  try {
    return await fn(dir);
  } finally {
    // best-effort cleanup handled by OS tmp management
  }
}

test('validation accepts valid records and optional ms', () => {
  const valid = validateTraceRecord({ ts: 1, prim_id: 'p', effect: 'io', ms: 2.5 });
  assert.equal(valid.ok, true);

  const withoutMs = validateTraceRecord({ ts: 2, prim_id: 'p2', effect: 'cpu' });
  assert.equal(withoutMs.ok, true);
});

test('validation rejects negative ms values', () => {
  const invalid = validateTraceRecord({ ts: 1, prim_id: 'p', effect: 'io', ms: -1 });
  assert.equal(invalid.ok, false);
  assert.ok(invalid.issues.some((issue) => issue.path === '.ms'));
});

test('ingest reports JSON parse errors with line numbers', async () => {
  await withTempDir(async (dir) => {
    const tracePath = join(dir, 'trace.jsonl');
    await writeFile(tracePath, '{"ts":1,"prim_id":"p","effect":"io"}\nnot json\n', 'utf8');
    const result = await ingestTraceFile(tracePath);
    assert.equal(result.records.length, 1);
    assert.equal(result.errors.length, 1);
    assert.equal(result.errors[0].line, 2);
  });
});

test('ingest flags internal empty lines only in strict mode', async () => {
  await withTempDir(async (dir) => {
    const tracePath = join(dir, 'trace.jsonl');
    await writeFile(
      tracePath,
      '{"ts":1,"prim_id":"p","effect":"io"}\n\n{"ts":2,"prim_id":"q","effect":"cpu"}\n\n',
      'utf8'
    );

    const original = process.env.TRACE_STRICT_EMPTY;
    try {
      delete process.env.TRACE_STRICT_EMPTY;
      const relaxed = await ingestTraceFile(tracePath);
      assert.equal(relaxed.errors.length, 0);
      assert.equal(relaxed.records.length, 2);

      process.env.TRACE_STRICT_EMPTY = '1';
      const strict = await ingestTraceFile(tracePath);
      assert.equal(strict.records.length, 2);
      assert.equal(strict.errors.length, 1);
      assert.equal(strict.errors[0].message, 'Empty line');
      assert.equal(strict.errors[0].line, 2);
    } finally {
      if (original === undefined) {
        delete process.env.TRACE_STRICT_EMPTY;
      } else {
        process.env.TRACE_STRICT_EMPTY = original;
      }
    }
  });
});

test('CLI export quotes fields with quotes and newlines', async () => {
  await withTempDir(async (dir) => {
    const tracePath = join(dir, 'trace.jsonl');
    const csvPath = join(dir, 'trace.csv');
    const records = [
      { ts: 1, prim_id: 'plain', effect: 'cpu', ms: 1.5 },
      { ts: 2, prim_id: 'with"quote', effect: `line
break`, ms: 2.75 }
    ];
    const jsonl = records.map((record) => JSON.stringify(record)).join('\n');
    await writeFile(tracePath, `${jsonl}\n`, 'utf8');

    const status = await new Promise((resolve, reject) => {
      const child = spawn('node', ['bin/trace.mjs', '--quiet', 'export', '--in', tracePath, '--csv', csvPath], {
        cwd: packageRoot,
        stdio: ['ignore', 'pipe', 'pipe']
      });
      let stdout = '';
      let stderr = '';
      child.stdout.on('data', (chunk) => {
        stdout += chunk.toString();
      });
      child.stderr.on('data', (chunk) => {
        stderr += chunk.toString();
      });
      child.on('close', (code) => {
        if (code === 0) {
          try {
            resolve(JSON.parse(stdout.trim()));
          } catch (error) {
            reject(error);
          }
        } else {
          reject(new Error(`CLI failed: ${stderr}`));
        }
      });
    });

    assert.equal(status.ok, true);
    assert.equal(status.kind, 'trace');
    assert.equal(status.rows, 2);

    const csv = await readFile(csvPath, 'utf8');
    assert.ok(csv.startsWith('ts,prim_id,effect,ms\n'));
    assert.ok(csv.endsWith('\n'));
    assert.ok(csv.includes('"with""quote"'));
    const newlineSubstring = `"line
break"`;
    assert.ok(csv.includes(newlineSubstring));
  });
});
