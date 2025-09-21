import test from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { spawnSync } from 'node:child_process';

const ROOT = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..');
const IR_PATH = path.join(ROOT, 'out/0.4/ir/signing.ir.json');
const OUT_DIR = path.join(ROOT, 'out/0.4/codegen-rs/signing');
const PARITY_REPORT = path.join(ROOT, 'out/0.4/parity/ts-rs/report.json');

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
  const env = { ...process.env };
  delete env.LOCAL_RUST;
  return spawnSync(process.execPath, ['scripts/generate-rs-run.mjs', IR_PATH, '-o', OUT_DIR], {
    cwd: ROOT,
    stdio: 'inherit',
    env,
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
  const adaptersPath = path.join(OUT_DIR, 'src', 'adapters.rs');
  const runPath = path.join(OUT_DIR, 'src', 'run.rs');
  const irJsonPath = path.join(OUT_DIR, 'src', 'ir.json');

  assert.ok(fs.existsSync(cargoPath), 'Cargo.toml should exist');
  assert.ok(fs.existsSync(pipelinePath), 'pipeline.rs should exist');
  assert.ok(fs.existsSync(adaptersPath), 'adapters.rs should exist');
  assert.ok(fs.existsSync(runPath), 'run.rs should exist');
  assert.ok(fs.existsSync(irJsonPath), 'ir.json should exist');

  const first = {
    cargo: fs.readFileSync(cargoPath, 'utf8'),
    pipe: fs.readFileSync(pipelinePath, 'utf8'),
    adapters: fs.readFileSync(adaptersPath, 'utf8'),
    run: fs.readFileSync(runPath, 'utf8'),
    ir: fs.readFileSync(irJsonPath, 'utf8'),
  };

  assert.ok(first.pipe.includes('pub fn run_pipeline'), 'pipeline should expose run_pipeline');

  // second generate (determinism)
  const secondRun = runGenerator();
  assert.equal(secondRun.status, 0, 'second generate should also exit 0');

  const second = {
    cargo: fs.readFileSync(cargoPath, 'utf8'),
    pipe: fs.readFileSync(pipelinePath, 'utf8'),
    adapters: fs.readFileSync(adaptersPath, 'utf8'),
    run: fs.readFileSync(runPath, 'utf8'),
    ir: fs.readFileSync(irJsonPath, 'utf8'),
  };

  assert.equal(first.cargo, second.cargo, 'Cargo.toml must be byte-identical');
  assert.equal(first.pipe, second.pipe, 'pipeline.rs must be byte-identical');
  assert.equal(first.adapters, second.adapters, 'adapters.rs must be byte-identical');
  assert.equal(first.run, second.run, 'run.rs must be byte-identical');
  assert.equal(first.ir, second.ir, 'ir.json must be byte-identical');

  // optional local cargo build (not required in CI)
  if (process.env.LOCAL_RUST) {
    const result = spawnSync('cargo', ['build'], { cwd: OUT_DIR, stdio: 'inherit' });
    assert.equal(result.status, 0, 'cargo build should succeed locally');
  }
});

test(
  'cross parity matches TypeScript trace when LOCAL_RUST=1',
  { skip: process.env.LOCAL_RUST !== '1' },
  () => {
    const result = spawnSync(
      process.execPath,
      ['scripts/cross-parity-ts-rs.mjs', 'examples/flows/run_publish.tf'],
      {
        cwd: ROOT,
        stdio: 'inherit',
        env: { ...process.env, LOCAL_RUST: '1' },
      },
    );
    assert.equal(result.status, 0, 'cross parity script should succeed');
    assert.ok(fs.existsSync(PARITY_REPORT), 'parity report should exist');
    const report = JSON.parse(fs.readFileSync(PARITY_REPORT, 'utf8'));
    assert.equal(report.equal, true, 'expected parity to hold when LOCAL_RUST=1');
  },
);
