// @tf-test kind=infra area=runtime speed=fast deps=node

import assert from 'node:assert/strict';
import test from 'node:test';
import { execFile } from 'node:child_process';
import { promisify } from 'node:util';
import { mkdtemp, writeFile, rm, readFile } from 'node:fs/promises';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { fileURLToPath } from 'node:url';

const execFileAsync = promisify(execFile);
const testDir = fileURLToPath(new URL('.', import.meta.url));
const packageRoot = join(testDir, '..');
const cliPath = join(packageRoot, 'bin', 'cli.mjs');

async function runCli(args, envOverrides = {}) {
  const env = { ...process.env, ...envOverrides };
  await execFileAsync(process.execPath, [cliPath, ...args], {
    cwd: packageRoot,
    env,
    maxBuffer: 10 * 1024 * 1024,
  });
}

async function readJson(path) {
  const body = await readFile(path, 'utf8');
  return { body, json: JSON.parse(body) };
}

async function readJsonl(path) {
  const body = await readFile(path, 'utf8');
  const trimmed = body.trimEnd();
  const lines = trimmed.length === 0 ? [] : trimmed.split('\n');
  return {
    body,
    items: lines.map(line => JSON.parse(line)),
  };
}

function normalizeTraceItems(traceItems) {
  return traceItems.map(item => ({
    prim_id: item?.prim_id ?? null,
    effect: item?.effect ?? null,
  }));
}

test('WASM engine matches stub trace ordering', async () => {
  const dir = await mkdtemp(join(tmpdir(), 'tf-run-wasm-'));
  try {
    const irPath = join(dir, 'sample.ir.json');
    const ir = {
      primitives: [
        { prim_id: 'tf:pure/identity@1', effect: 'identity' },
        { prim: 'tf:resource/write-object@1', effect: 'write object' },
        'tf:integration/publish-topic@1',
      ],
    };
    await writeFile(irPath, JSON.stringify(ir), 'utf8');

    const wasmStatusPath = join(dir, 'status-wasm.json');
    const wasmTracePath = join(dir, 'trace-wasm.jsonl');
    const stubStatusPath = join(dir, 'status-stub.json');
    const stubTracePath = join(dir, 'trace-stub.jsonl');

    await runCli(['--ir', irPath, '--status', wasmStatusPath, '--trace', wasmTracePath]);
    await runCli(
      ['--ir', irPath, '--status', stubStatusPath, '--trace', stubTracePath],
      { TF_RUN_WASM_DISABLE_WASM: '1' },
    );

    const wasmTrace = await readJsonl(wasmTracePath);
    const stubTrace = await readJsonl(stubTracePath);

    assert.ok(wasmTrace.body.endsWith('\n'), 'WASM trace file should end with newline');
    assert.ok(stubTrace.body.endsWith('\n'), 'stub trace file should end with newline');
    assert.deepEqual(
      normalizeTraceItems(wasmTrace.items),
      normalizeTraceItems(stubTrace.items),
    );
  } finally {
    await rm(dir, { recursive: true, force: true });
  }
});

test('status and trace outputs are newline-terminated', async () => {
  const dir = await mkdtemp(join(tmpdir(), 'tf-run-wasm-'));
  try {
    const statusPath = join(dir, 'status.json');
    const tracePath = join(dir, 'trace.jsonl');
    const irPath = join(dir, 'sample.ir.json');
    const ir = {
      primitives: [
        { prim_id: 'tf:observability/emit-metric@1' },
        { prim_id: 'tf:network/publish@1', effect: 'publish' },
      ],
    };

    await writeFile(irPath, JSON.stringify(ir), 'utf8');

    await runCli(
      ['--ir', irPath, '--status', statusPath, '--trace', tracePath],
      { TF_RUN_WASM_DISABLE_WASM: '1' },
    );

    const status = await readJson(statusPath);
    const trace = await readJsonl(tracePath);

    assert.ok(status.body.endsWith('\n'), 'status JSON should end with a newline');
    assert.ok(trace.body.endsWith('\n'), 'trace JSONL should end with a newline');
    assert.ok(status.body.includes('\n  "ok"'), 'status JSON should be pretty formatted');

    assert.equal(status.json.ok, true);
    assert.equal(status.json.engine, 'tf-eval-stub');
    assert.equal(status.json.bytes, Buffer.byteLength(JSON.stringify(ir), 'utf8'));

    const traceItems = normalizeTraceItems(trace.items);
    assert.equal(traceItems.length, ir.primitives.length);
    for (const item of traceItems) {
      assert.ok(typeof item.prim_id === 'string' || item.prim_id === null);
    }
  } finally {
    await rm(dir, { recursive: true, force: true });
  }
});
