import test from 'node:test';
import { spawnSync } from 'node:child_process';
import { rmSync, readFileSync } from 'node:fs';
import path from 'node:path';
import { strict as assert } from 'node:assert';
import { fileURLToPath } from 'node:url';

const ROOT = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..');
const PILOT_OUT = 'out/0.4/pilot-full/parity-test';
const T5_OUT = 'out/t5-full/parity-test';
const PARITY_OUT = 'out/0.4/parity/pilot-full-test';

function run(cmd, args, env) {
  const result = spawnSync(cmd, args, {
    stdio: 'inherit',
    cwd: ROOT,
    env: { ...process.env, ...env },
  });
  assert.equal(result.status, 0, `${cmd} ${args.join(' ')} exited with ${result.status}`);
}

const shouldRun = process.env.TF_PILOT_FULL === '1';

test('pilot full parity matches t5 outputs', { skip: !shouldRun }, () => {
  const env = {
    TF_PILOT_SEED: '42',
    TF_PILOT_SLICE: '0:50:1',
    PILOT_FULL_OUT_DIR: PILOT_OUT,
    T5_FULL_OUT_DIR: T5_OUT,
    PILOT_FULL_PARITY_DIR: PARITY_OUT,
  };

  rmSync(path.join(ROOT, PILOT_OUT), { recursive: true, force: true });
  rmSync(path.join(ROOT, T5_OUT), { recursive: true, force: true });
  rmSync(path.join(ROOT, PARITY_OUT), { recursive: true, force: true });

  run('pnpm', ['--filter', '@tf-lang/pilot-core', 'build'], env);
  run('pnpm', ['--filter', '@tf-lang/pilot-replay', 'build'], env);
  run('pnpm', ['--filter', '@tf-lang/pilot-strategy', 'build'], env);
  run('pnpm', ['--filter', '@tf-lang/pilot-risk', 'build'], env);
  run('node', ['scripts/t5-build-run.mjs'], env);
  run('node', ['scripts/pilot-full-build-run.mjs'], env);
  run('node', ['scripts/pilot-full-parity.mjs'], env);

  const reportPath = path.join(ROOT, PARITY_OUT, 'report.json');
  const reportRaw1 = readFileSync(reportPath, 'utf8');
  const report1 = JSON.parse(reportRaw1);
  assert.equal(report1.equal, true, 'parity report should signal equality');
  assert.deepEqual(report1.diff, [], 'parity diff should be empty');

  run('node', ['scripts/pilot-full-parity.mjs'], env);
  const reportRaw2 = readFileSync(reportPath, 'utf8');
  assert.equal(reportRaw2, reportRaw1, 'parity report should be stable across runs');
});
