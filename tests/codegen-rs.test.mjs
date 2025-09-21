import test from 'node:test';
import assert from 'node:assert/strict';
import { rm, readFile } from 'node:fs/promises';
import { existsSync } from 'node:fs';
import { spawn, spawnSync } from 'node:child_process';
import { fileURLToPath } from 'node:url';
import { resolve, dirname, join } from 'node:path';

const ROOT = resolve(dirname(fileURLToPath(import.meta.url)), '..');
const IR_PATH = join(ROOT, 'out/0.4/ir/signing.ir.json');
const OUT_DIR = join(ROOT, 'out/0.4/codegen-rs/signing');

async function runGenerator() {
  return new Promise((resolvePromise, rejectPromise) => {
    const child = spawn(
      'node',
      ['scripts/generate-rs.mjs', IR_PATH, '-o', OUT_DIR],
      { cwd: ROOT, stdio: ['inherit', 'pipe', 'inherit'] }
    );

    let stdout = '';
    child.stdout.on('data', (chunk) => {
      stdout += chunk.toString();
    });

    child.on('error', rejectPromise);
    child.on('exit', (code) => {
      if (code === 0) {
        resolvePromise(stdout.trim());
      } else {
        rejectPromise(new Error(`generator exited with code ${code}`));
      }
    });
  });
}

test('rust codegen emits deterministic scaffold', async () => {
  assert.ok(existsSync(IR_PATH), 'expected signing IR fixture');

  await rm(OUT_DIR, { recursive: true, force: true });

  const firstStdout = await runGenerator();
  assert.match(firstStdout, /wrote .*signing/, 'expected generator to report output path');

  const cargoPath = join(OUT_DIR, 'Cargo.toml');
  const pipelinePath = join(OUT_DIR, 'src/pipeline.rs');

  const firstCargo = await readFile(cargoPath, 'utf8');
  const firstPipeline = await readFile(pipelinePath, 'utf8');

  assert.ok(firstPipeline.includes('pub fn run_pipeline'), 'pipeline should expose run_pipeline');
  assert.ok(firstPipeline.includes('Crypto'), 'signing flow should require Crypto trait');

  const secondStdout = await runGenerator();
  assert.match(secondStdout, /wrote .*signing/, 'expected generator to report output path on rerun');

  const secondCargo = await readFile(cargoPath, 'utf8');
  const secondPipeline = await readFile(pipelinePath, 'utf8');

  assert.equal(firstCargo, secondCargo, 'Cargo.toml should be deterministic');
  assert.equal(firstPipeline, secondPipeline, 'pipeline.rs should be deterministic');

  if (process.env.LOCAL_RUST) {
    const result = spawnSync('cargo', ['build'], { cwd: OUT_DIR, stdio: 'inherit' });
    assert.equal(result.status, 0, 'cargo build should succeed locally');
  }
});
