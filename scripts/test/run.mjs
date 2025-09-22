import { spawn, spawnSync } from 'node:child_process';
import path from 'node:path';
import { fileURLToPath } from 'node:url';

import { discoverTests } from './discover.mjs';
import { sortTests, writeJsonCanonical } from './utils.mjs';

const ROOT = path.resolve(fileURLToPath(new URL('../../', import.meta.url)));
const OUT_DIR = path.join(ROOT, 'out', '0.4', 'tests');

function parseArgs(argv) {
  const filters = { kind: [], speed: [], deps: [] };
  let allowMissingDeps = false;
  for (let i = 0; i < argv.length; i += 1) {
    const arg = argv[i];
    if (arg === '--kind' || arg === '--speed' || arg === '--deps') {
      const value = argv[i + 1];
      if (!value) {
        throw new Error(`Missing value for ${arg}`);
      }
      filters[arg.slice(2)].push(value);
      i += 1;
    } else if (arg === '--allow-missing-deps') {
      allowMissingDeps = true;
    } else {
      throw new Error(`Unknown argument: ${arg}`);
    }
  }
  return { filters, allowMissingDeps };
}

const depAvailability = new Map();

depAvailability.set('node', true);

depAvailability.set('rust', checkCargo());

function checkCargo() {
  const result = spawnSync('cargo', ['--version'], { stdio: 'ignore' });
  return result.status === 0;
}

function checkDeps(test, allowMissing) {
  const missing = test.deps.filter((dep) => !depAvailability.get(dep));
  if (missing.length === 0) {
    return { status: 'ok', missing: [] };
  }
  if (allowMissing) {
    return { status: 'skip', missing };
  }
  return { status: 'error', missing };
}

function runCommand(command, args, options = {}) {
  return new Promise((resolve) => {
    const child = spawn(command, args, {
      cwd: options.cwd ?? ROOT,
      env: options.env ?? process.env,
      stdio: 'inherit',
    });
    child.on('exit', (code) => {
      resolve(code === 0);
    });
    child.on('error', (err) => {
      console.error(err);
      resolve(false);
    });
  });
}

async function runTest(test) {
  if (test.runner.type === 'node') {
    return runCommand(process.execPath, ['--test', test.file]);
  }
  if (test.runner.type === 'vitest') {
    const pkgDir = test.runner.packageDir;
    const testPath = test.runner.testPath;
    return runCommand(
      'pnpm',
      ['exec', 'vitest', 'run', '--dir', '.', testPath],
      { cwd: path.join(ROOT, pkgDir) },
    );
  }
  if (test.runner.type === 'cargo') {
    const manifest = test.runner.manifestPath;
    const name = test.runner.testName;
    return runCommand('cargo', ['test', '--manifest-path', manifest, '--test', name]);
  }
  throw new Error(`Unsupported runner: ${test.runner.type}`);
}

async function main() {
  const { filters, allowMissingDeps } = parseArgs(process.argv.slice(2));
  const tests = await discoverTests();
  const selected = sortTests(
    tests.filter((test) => {
      if (filters.kind.length && !filters.kind.includes(test.kind)) return false;
      if (filters.speed.length && !filters.speed.includes(test.speed)) return false;
      if (filters.deps.length && !filters.deps.every((dep) => test.deps.includes(dep))) return false;
      return true;
    }),
  );

  const summary = {
    ok: true,
    selected: selected.length,
    run: { node: 0, vitest: 0, cargo: 0 },
    skipped: [],
  };

  if (selected.length === 0) {
    console.log('No tests matched the provided filters.');
  }

  for (const test of selected) {
    const depCheck = checkDeps(test, allowMissingDeps);
    if (depCheck.status === 'skip') {
      summary.skipped.push({ file: test.file, reason: `missing ${depCheck.missing.join(', ')}` });
      continue;
    }
    if (depCheck.status === 'error') {
      summary.skipped.push({ file: test.file, reason: `missing ${depCheck.missing.join(', ')} (required)` });
      summary.ok = false;
      continue;
    }
    const success = await runTest(test);
    summary.run[test.runner.type] += 1;
    if (!success) {
      summary.ok = false;
    }
  }

  summary.skipped.sort((a, b) => a.file.localeCompare(b.file));

  const manifestPath = path.join(OUT_DIR, 'manifest.json');
  await writeJsonCanonical(manifestPath, summary);
  if (!summary.ok) {
    process.exitCode = 1;
  }
}

main().catch((err) => {
  console.error(err);
  process.exitCode = 1;
});
