import test from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { spawnSync } from 'node:child_process';

const ROOT = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..');
const IR_PATH = path.join(ROOT, 'out/0.4/ir/signing.ir.json');
const OUT_DIR = path.join(ROOT, 'out/0.4/codegen-rs/signing');

function runGenerator() {
  return spawnSync('node', ['scripts/generate-rs.mjs', IR_PATH, '-o', OUT_DIR], {
    cwd: ROOT,
    stdio: 'inherit',
  });
}

test('rust codegen emits deterministic scaffold', () => {
  if (!fs.existsSync(IR_PATH)) {
    fs.mkdirSync(path.dirname(IR_PATH), { recursive: true });
    const parse = spawnSync('node', ['packages/tf-compose/bin/tf.mjs', 'parse', 'examples/flows/signing.tf', '-o', IR_PATH], {
      cwd: ROOT,
      stdio: 'inherit',
    });
    assert.equal(parse.status, 0, 'signing parse should succeed');
  }

  assert.ok(fs.existsSync(IR_PATH), 'expected signing IR fixture');

  fs.rmSync(OUT_DIR, { recursive: true, force: true });

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

  assert.ok(first.pipe.includes('pub fn run_pipeline'), 'pipeline should expose run_pipeline');
  assert.ok(first.pipe.includes('Crypto'), 'signing flow should require Crypto trait');

  const secondRun = runGenerator();
  assert.equal(secondRun.status, 0, 'second generate should also exit 0');

  const second = {
    cargo: fs.readFileSync(cargoPath, 'utf8'),
    pipe: fs.readFileSync(pipelinePath, 'utf8'),
  };

  assert.equal(first.cargo, second.cargo, 'Cargo.toml must be byte-identical');
  assert.equal(first.pipe, second.pipe, 'pipeline.rs must be byte-identical');

  if (process.env.LOCAL_RUST) {
    const result = spawnSync('cargo', ['build'], { cwd: OUT_DIR, stdio: 'inherit' });
    assert.equal(result.status, 0, 'cargo build should succeed locally');
  }
});
