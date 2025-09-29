// @tf-test kind=infra area=runtime speed=fast deps=node

import assert from 'node:assert/strict';
import test from 'node:test';
import { execFile } from 'node:child_process';
import { promisify } from 'node:util';
import { mkdtemp, writeFile, rm } from 'node:fs/promises';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { fileURLToPath } from 'node:url';

const execFileAsync = promisify(execFile);
const testDir = fileURLToPath(new URL('.', import.meta.url));
const packageRoot = join(testDir, '..');

async function runInIsolatedProcess(irPath, envOverrides = {}) {
  const env = { ...process.env, ...envOverrides };
  const script = `
    import { run } from './dist/index.js';
    const result = await run({ irPath: ${JSON.stringify(irPath)} });
    process.stdout.write(JSON.stringify(result));
  `;
  const { stdout } = await execFileAsync(process.execPath, ['--input-type=module', '--eval', script], {
    cwd: packageRoot,
    env,
    maxBuffer: 10 * 1024 * 1024,
  });
  return JSON.parse(stdout.toString());
}

test('wasm engine matches stub trace ordering', async () => {
  const dir = await mkdtemp(join(tmpdir(), 'tf-run-wasm-'));
  try {
    const irPath = join(dir, 'sample.ir.json');
    const ir = {
      primitives: [
        { prim_id: 'tf:pure/identity@1' },
        { prim: 'tf:resource/write-object@1' },
      ],
    };
    await writeFile(irPath, JSON.stringify(ir), 'utf8');

    const withWasm = await runInIsolatedProcess(irPath);
    const withStub = await runInIsolatedProcess(irPath, { TF_RUN_WASM_DISABLE_WASM: '1' });

    const normalize = trace => trace.map(item => ({
      prim_id: item.prim_id ?? null,
      effect: item.effect ?? null,
    }));

    assert.deepEqual(normalize(withWasm.trace), normalize(withStub.trace));
  } finally {
    await rm(dir, { recursive: true, force: true });
  }
});
