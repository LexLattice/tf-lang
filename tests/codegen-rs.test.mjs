import test from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { spawnSync } from 'node:child_process';

const ROOT = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..');
const IR_PATH = path.join(ROOT, 'out/0.4/ir/signing.ir.json');
const OUT_DIR = path.join(ROOT, 'out/0.4/codegen-rs/signing');
const GENERATE_SCRIPT = path.join(ROOT, 'scripts/generate-rs-run.mjs');
const PARITY_SCRIPT = path.join(ROOT, 'scripts/cross-parity-ts-rs.mjs');
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

function runGenerator(env = {}) {
  const mergedEnv = { ...process.env, ...env };
  const result = spawnSync(process.execPath, [GENERATE_SCRIPT, IR_PATH, '-o', OUT_DIR], {
    cwd: ROOT,
    stdio: 'inherit',
    env: mergedEnv,
  });
  return result;
}

test('rust codegen emits deterministic scaffold', () => {
  ensureSigningIr();
  assert.ok(fs.existsSync(IR_PATH), 'expected signing IR fixture');

  fs.rmSync(OUT_DIR, { recursive: true, force: true });

  const firstRun = runGenerator({ LOCAL_RUST: '0' });
  assert.equal(firstRun.status, 0, 'generator should exit 0 without cargo');

  const cargoPath = path.join(OUT_DIR, 'Cargo.toml');
  const libPath = path.join(OUT_DIR, 'src', 'lib.rs');
  const pipelinePath = path.join(OUT_DIR, 'src', 'pipeline.rs');
  const adaptersPath = path.join(OUT_DIR, 'src', 'adapters.rs');
  const runPath = path.join(OUT_DIR, 'src', 'bin', 'run.rs');
  const irCopyPath = path.join(OUT_DIR, 'ir.json');

  for (const file of [cargoPath, libPath, pipelinePath, adaptersPath, runPath, irCopyPath]) {
    assert.ok(fs.existsSync(file), `expected ${path.relative(ROOT, file)} to exist`);
  }

  const first = {
    cargo: fs.readFileSync(cargoPath, 'utf8'),
    lib: fs.readFileSync(libPath, 'utf8'),
    pipeline: fs.readFileSync(pipelinePath, 'utf8'),
    adapters: fs.readFileSync(adaptersPath, 'utf8'),
    run: fs.readFileSync(runPath, 'utf8'),
    ir: fs.readFileSync(irCopyPath, 'utf8'),
  };

  assert.ok(first.lib.includes('pub mod adapters'), 'lib.rs should expose adapters module');
  assert.ok(first.pipeline.includes('pub fn run_ir'), 'pipeline.rs should expose run_ir');
  assert.ok(first.run.includes('DEFAULT_IR'), 'run binary should embed default IR');
  for (const [name, content] of Object.entries(first)) {
    assert.ok(content.endsWith('\n'), `${name} should end with a trailing newline`);
  }

  const secondRun = runGenerator({ LOCAL_RUST: '0' });
  assert.equal(secondRun.status, 0, 'second generate should also exit 0');

  const second = {
    cargo: fs.readFileSync(cargoPath, 'utf8'),
    lib: fs.readFileSync(libPath, 'utf8'),
    pipeline: fs.readFileSync(pipelinePath, 'utf8'),
    adapters: fs.readFileSync(adaptersPath, 'utf8'),
    run: fs.readFileSync(runPath, 'utf8'),
    ir: fs.readFileSync(irCopyPath, 'utf8'),
  };

  assert.equal(first.cargo, second.cargo, 'Cargo.toml must be byte-identical');
  assert.equal(first.lib, second.lib, 'lib.rs must be byte-identical');
  assert.equal(first.pipeline, second.pipeline, 'pipeline.rs must be byte-identical');
  assert.equal(first.adapters, second.adapters, 'adapters.rs must be byte-identical');
  assert.equal(first.run, second.run, 'run.rs must be byte-identical');
  assert.equal(first.ir, second.ir, 'ir.json must be byte-identical');

  if (process.env.LOCAL_RUST === '1') {
    const cargoRun = runGenerator({ LOCAL_RUST: '1' });
    assert.equal(cargoRun.status, 0, 'cargo-backed generation should succeed locally');
    const tracePath = path.join(OUT_DIR, 'out', 'trace.jsonl');
    assert.ok(fs.existsSync(tracePath), 'expected cargo run to emit trace.jsonl');
  }
});

test('ts and rust traces align for run_publish when rust is available', async (t) => {
  if (process.env.LOCAL_RUST !== '1') {
    t.skip('LOCAL_RUST not set');
    return;
  }

  const result = spawnSync(process.execPath, [PARITY_SCRIPT, 'examples/flows/run_publish.tf'], {
    cwd: ROOT,
    stdio: 'inherit',
    env: process.env,
  });
  assert.equal(result.status, 0, 'parity script should exit 0');
  assert.ok(fs.existsSync(PARITY_REPORT), 'expected parity report');
  const report = JSON.parse(fs.readFileSync(PARITY_REPORT, 'utf8'));
  assert.equal(report.equal, true, 'expected TS and Rust traces to match');
});
