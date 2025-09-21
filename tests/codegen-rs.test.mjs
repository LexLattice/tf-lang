import test from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { spawnSync } from 'node:child_process';
import { generateRustCrate } from '../scripts/generate-rs.mjs';

const ROOT = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..');
const IR_PATH = path.join(ROOT, 'out/0.4/ir/signing.ir.json');
const OUT_DIR = path.join(ROOT, 'out/0.4/codegen-rs/signing');

async function ensureSigningIr() {
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

test('rust codegen emits deterministic scaffold', async () => {
  await ensureSigningIr();
  fs.rmSync(OUT_DIR, { recursive: true, force: true });

  await generateRustCrate(IR_PATH, OUT_DIR);
  const paths = {
    cargo: path.join(OUT_DIR, 'Cargo.toml'),
    pipeline: path.join(OUT_DIR, 'src/pipeline.rs'),
    adapters: path.join(OUT_DIR, 'src/adapters.rs'),
    run: path.join(OUT_DIR, 'src/run.rs'),
    lib: path.join(OUT_DIR, 'src/lib.rs'),
    ir: path.join(OUT_DIR, 'ir.json'),
  };

  for (const key of Object.keys(paths)) {
    assert.ok(fs.existsSync(paths[key]), `missing ${key}`);
  }

  const first = {
    cargo: fs.readFileSync(paths.cargo, 'utf8'),
    pipeline: fs.readFileSync(paths.pipeline, 'utf8'),
    adapters: fs.readFileSync(paths.adapters, 'utf8'),
    run: fs.readFileSync(paths.run, 'utf8'),
    lib: fs.readFileSync(paths.lib, 'utf8'),
    ir: fs.readFileSync(paths.ir, 'utf8'),
  };

  assert.ok(first.pipeline.includes('TraceEntry'), 'pipeline should define TraceEntry');
  assert.ok(first.run.includes('include_str!("../ir.json")'), 'run.rs should include baked IR');

  await generateRustCrate(IR_PATH, OUT_DIR);
  const second = {
    cargo: fs.readFileSync(paths.cargo, 'utf8'),
    pipeline: fs.readFileSync(paths.pipeline, 'utf8'),
    adapters: fs.readFileSync(paths.adapters, 'utf8'),
    run: fs.readFileSync(paths.run, 'utf8'),
    lib: fs.readFileSync(paths.lib, 'utf8'),
    ir: fs.readFileSync(paths.ir, 'utf8'),
  };

  assert.equal(first.cargo, second.cargo, 'Cargo.toml must be deterministic');
  assert.equal(first.pipeline, second.pipeline, 'pipeline.rs must be deterministic');
  assert.equal(first.adapters, second.adapters, 'adapters.rs must be deterministic');
  assert.equal(first.run, second.run, 'run.rs must be deterministic');
  assert.equal(first.lib, second.lib, 'lib.rs must be deterministic');
  assert.equal(first.ir, second.ir, 'ir.json must be deterministic');

  if (process.env.LOCAL_RUST) {
    const result = spawnSync('cargo', ['run', '--', '--ir', IR_PATH], { cwd: OUT_DIR, stdio: 'inherit' });
    assert.equal(result.status, 0, 'cargo run should succeed locally');
    const tracePath = path.join(OUT_DIR, 'out', 'trace.jsonl');
    assert.ok(fs.existsSync(tracePath), 'trace.jsonl should exist after cargo run');
  }
});
