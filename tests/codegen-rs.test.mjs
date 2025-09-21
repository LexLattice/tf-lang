import test from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { spawnSync } from 'node:child_process';

const ROOT = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..');
const IR_PATH = path.join(ROOT, 'out/0.4/ir/signing.ir.json');
const OUT_DIR = path.join(ROOT, 'out/0.4/codegen-rs/signing');

function ensureSigningIr() {
  if (fs.existsSync(IR_PATH)) return;

  fs.mkdirSync(path.dirname(IR_PATH), { recursive: true });
  const result = spawnSync(process.execPath, [
    'packages/tf-compose/bin/tf.mjs',
    'parse',
    'examples/flows/signing.tf',
    '-o',
    IR_PATH,
  ], { cwd: ROOT, stdio: 'inherit' });

  assert.equal(result.status, 0, 'failed to generate signing IR fixture');
  assert.ok(fs.existsSync(IR_PATH), 'expected signing IR fixture after generation');
}

function runGenerator() {
  return spawnSync(process.execPath, ['scripts/generate-rs.mjs', IR_PATH, '-o', OUT_DIR], {
    cwd: ROOT,
    stdio: 'inherit',
  });
}

test('rust codegen emits deterministic scaffold', () => {
  // ensure we have the IR fixture available
  ensureSigningIr();
  assert.ok(fs.existsSync(IR_PATH), 'expected signing IR fixture');

  // clean output dir
  fs.rmSync(OUT_DIR, { recursive: true, force: true });

  // first generate
  const firstRun = runGenerator();
  assert.equal(firstRun.status, 0, 'generator should exit 0 without cargo');

  const cargoPath = path.join(OUT_DIR, 'Cargo.toml');
  const pipelinePath = path.join(OUT_DIR, 'src', 'pipeline.rs');

  assert.ok(fs.existsSync(cargoPath), 'Cargo.toml should exist');
  assert.ok(fs.existsSync(pipelinePath), 'pipeline.rs should exist');

  const first = {
    cargo: fs.readFileSync(cargoPath, 'utf8'),
    pipe: fs.readFileSync(pipelinePath, 'utf8'),
  };

  // pipeline function and trait bound presence (signing → Crypto)
  assert.ok(first.pipe.includes('pub fn run_pipeline'), 'pipeline should expose run_pipeline');
  assert.ok(first.pipe.includes('Crypto'), 'signing flow should require Crypto trait');

  // second generate (determinism)
  const secondRun = runGenerator();
  assert.equal(secondRun.status, 0, 'second generate should also exit 0');

  const second = {
    cargo: fs.readFileSync(cargoPath, 'utf8'),
    pipe: fs.readFileSync(pipelinePath, 'utf8'),
  };

  assert.equal(first.cargo, second.cargo, 'Cargo.toml must be byte-identical');
  assert.equal(first.pipe, second.pipe, 'pipeline.rs must be byte-identical');

  // optional local cargo build (not required in CI)
  if (process.env.LOCAL_RUST) {
    const result = spawnSync('cargo', ['build'], { cwd: OUT_DIR, stdio: 'inherit' });
    assert.equal(result.status, 0, 'cargo build should succeed locally');
  }
});
