import { spawn, spawnSync } from 'node:child_process';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { performance } from 'node:perf_hooks';

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
depAvailability.set('z3', checkZ3());

function checkCargo() {
  const result = spawnSync('cargo', ['--version'], { stdio: 'ignore' });
  return result.status === 0;
}

function checkZ3() {
  const result = spawnSync('z3', ['-version'], { stdio: 'ignore' });
  return result.status === 0;
}

function checkDeps(test, allowMissing) {
  const required = new Set(test.deps || []);
  if (test?.runner?.type === 'cargo') {
    required.add('rust');
  }
  const missing = [...required].filter((dep) => !depAvailability.get(dep));
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
  let { filters, allowMissingDeps } = parseArgs(process.argv.slice(2));
  // Fast runs should tolerate missing heavy toolchains (e.g., cargo).
  if (!allowMissingDeps && filters.speed.includes('fast')) {
    allowMissingDeps = true;
  }
  const debugFlags = process.env.TEST_RUN_DEBUG === '1';
  if (debugFlags) {
    console.log(`[tests] filters=${JSON.stringify(filters)} allowMissingDeps=${allowMissingDeps}`);
  }
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
    durations: {
      totalMs: 0,
      byRunner: { node: 0, vitest: 0, cargo: 0 },
      byTest: [],
    },
  };

  if (selected.length === 0) {
    console.log('No tests matched the provided filters.');
  }

  let failedCount = 0;
  let missingRequiredCount = 0;

  for (const test of selected) {
    const depCheck = checkDeps(test, allowMissingDeps);
    if (depCheck.status === 'skip') {
      if (debugFlags) {
        console.log(`[tests] skip ${test.file} (missing ${depCheck.missing.join(', ')})`);
      }
      summary.skipped.push({ file: test.file, reason: `missing ${depCheck.missing.join(', ')}` });
      continue;
    }
    if (depCheck.status === 'error') {
      if (debugFlags) {
        console.error(`[tests] missing required deps: ${test.file} -> ${depCheck.missing.join(', ')}`);
      }
      summary.skipped.push({ file: test.file, reason: `missing ${depCheck.missing.join(', ')} (required)` });
      missingRequiredCount += 1;
      continue;
    }
    if (debugFlags) {
      console.log(`[tests] run ${test.file}`);
    }
    const start = performance.now();
    const success = await runTest(test);
    const durationMs = performance.now() - start;
    summary.run[test.runner.type] += 1;
    summary.durations.byRunner[test.runner.type] += durationMs;
    summary.durations.totalMs += durationMs;
    summary.durations.byTest.push({
      file: test.file,
      runner: test.runner.type,
      ms: durationMs,
    });
    if (!success) {
      failedCount += 1;
      console.error(`[tests] failure: ${test.file}`);
    }
  }

  summary.skipped.sort((a, b) => a.file.localeCompare(b.file));

  summary.ok = failedCount === 0 && missingRequiredCount === 0;

  summary.durations.totalMs = Number(summary.durations.totalMs.toFixed(3));
  for (const runner of Object.keys(summary.durations.byRunner)) {
    summary.durations.byRunner[runner] = Number(summary.durations.byRunner[runner].toFixed(3));
  }
  summary.durations.byTest = summary.durations.byTest.map((entry) => ({
    ...entry,
    ms: Number(entry.ms.toFixed(3)),
  }));

  const manifestPath = path.join(OUT_DIR, 'manifest.json');
  await writeJsonCanonical(manifestPath, summary);
  if (debugFlags) {
    console.log('[tests] summary', JSON.stringify(summary));
  }
  process.exitCode = failedCount > 0 ? 1 : 0;
  console.log(
    `[tests] selected=${summary.selected} run=${JSON.stringify(summary.run)} skipped=${summary.skipped.length} failed=${failedCount} missingRequired=${missingRequiredCount} ok=${summary.ok}`,
  );
}

main().catch((err) => {
  console.error(err);
  process.exitCode = 1;
});
