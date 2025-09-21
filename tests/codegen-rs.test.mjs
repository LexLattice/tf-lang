import test from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { spawnSync } from 'node:child_process';

const ROOT = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..');
const IR_PATH = path.join(ROOT, 'out/0.4/ir/signing.ir.json');
const OUT_DIR = path.join(ROOT, 'out/0.4/codegen-rs/signing');
const GENERATOR = 'scripts/generate-rs-run.mjs';

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
  return spawnSync(process.execPath, [GENERATOR, IR_PATH, '-o', OUT_DIR], {
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
  const libPath = path.join(OUT_DIR, 'src', 'lib.rs');
  const adaptersPath = path.join(OUT_DIR, 'src', 'adapters.rs');
  const pipelinePath = path.join(OUT_DIR, 'src', 'pipeline.rs');
  const runPath = path.join(OUT_DIR, 'src', 'run.rs');

  for (const file of [cargoPath, libPath, adaptersPath, pipelinePath, runPath]) {
    assert.ok(fs.existsSync(file), `${path.relative(OUT_DIR, file)} should exist`);
  }

  const first = {
    cargo: fs.readFileSync(cargoPath, 'utf8'),
    lib: fs.readFileSync(libPath, 'utf8'),
    adapters: fs.readFileSync(adaptersPath, 'utf8'),
    pipeline: fs.readFileSync(pipelinePath, 'utf8'),
    run: fs.readFileSync(runPath, 'utf8'),
  };

  assert.ok(first.pipeline.includes('pub fn baked_ir()'), 'pipeline should expose baked_ir');
  assert.ok(first.pipeline.includes('TraceRecord'), 'pipeline should define TraceRecord');
  assert.ok(first.pipeline.includes('tf:security/sign-data@1'), 'pipeline should embed canonical prim ids');
  assert.ok(first.adapters.includes('InMemoryAdapters'), 'adapters module should expose InMemoryAdapters');
  assert.ok(first.run.includes('TraceEmitter'), 'run binary should emit trace events');

  // second generate (determinism)
  const secondRun = runGenerator();
  assert.equal(secondRun.status, 0, 'second generate should also exit 0');

  const second = {
    cargo: fs.readFileSync(cargoPath, 'utf8'),
    lib: fs.readFileSync(libPath, 'utf8'),
    adapters: fs.readFileSync(adaptersPath, 'utf8'),
    pipeline: fs.readFileSync(pipelinePath, 'utf8'),
    run: fs.readFileSync(runPath, 'utf8'),
  };

  assert.equal(first.cargo, second.cargo, 'Cargo.toml must be byte-identical');
  assert.equal(first.lib, second.lib, 'lib.rs must be deterministic');
  assert.equal(first.adapters, second.adapters, 'adapters.rs must be deterministic');
  assert.equal(first.pipeline, second.pipeline, 'pipeline.rs must be deterministic');
  assert.equal(first.run, second.run, 'run.rs must be deterministic');

  // optional local cargo build (not required in CI)
  if (process.env.LOCAL_RUST) {
    const result = spawnSync('cargo', ['build'], { cwd: OUT_DIR, stdio: 'inherit' });
    assert.equal(result.status, 0, 'cargo build should succeed locally');
  }
});
