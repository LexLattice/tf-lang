import test from 'node:test';
import { spawnSync } from 'node:child_process';
import { rmSync, readFileSync } from 'node:fs';
import { join, dirname } from 'node:path';
import { fileURLToPath } from 'node:url';

const here = dirname(fileURLToPath(import.meta.url));
const rootDir = join(here, '..');
const pilotOut = join(rootDir, 'out', '0.4', 'pilot-full');
const t5Out = join(rootDir, 'out', 't5-full');
const reportPath = join(rootDir, 'out', '0.4', 'parity', 'full', 'report.json');

function run(command, args, env) {
  const result = spawnSync(command, args, {
    cwd: rootDir,
    stdio: 'inherit',
    env: { ...process.env, ...env },
  });
  if (result.status !== 0) {
    throw new Error(`${command} ${args.join(' ')} failed with ${result.status}`);
  }
}

test('pilot full parity', { skip: process.env.TF_PILOT_FULL !== '1' }, () => {
  rmSync(pilotOut, { recursive: true, force: true });
  rmSync(t5Out, { recursive: true, force: true });
  rmSync(join(rootDir, 'out', '0.4', 'parity', 'full'), { recursive: true, force: true });

  const env = {
    TF_PILOT_FULL: '1',
    TF_PILOT_SEED: process.env.TF_PILOT_SEED ?? '42',
    TF_PILOT_SLICE: process.env.TF_PILOT_SLICE ?? '0:50:1',
  };

  run('node', ['scripts/t5-build-run.mjs'], env);
  run('node', ['scripts/pilot-full-build-run.mjs'], env);
  run('node', ['scripts/pilot-full-parity.mjs'], {});

  const report = JSON.parse(readFileSync(reportPath, 'utf8'));
  if (report.equal !== true) {
    throw new Error('pilot full parity report expected equal=true');
  }

  run('node', ['scripts/pilot-full-parity.mjs'], {});
  const report2 = JSON.parse(readFileSync(reportPath, 'utf8'));
  if (JSON.stringify(report2) !== JSON.stringify(report)) {
    throw new Error('pilot full parity report should be stable across runs');
  }
});
