import { promises as fs } from 'node:fs';
import path from 'node:path';
import { spawn } from 'node:child_process';

import { ROOT, discoverTests } from './utils.mjs';

function parseArgs(argv) {
  const filters = { kind: [], area: [], speed: [], deps: [] };
  let allowMissingDeps = false;
  for (let i = 0; i < argv.length; i += 1) {
    const arg = argv[i];
    if (arg === '--allow-missing-deps') {
      allowMissingDeps = true;
      continue;
    }
    if (!arg.startsWith('--')) {
      throw new Error(`Unknown argument: ${arg}`);
    }
    const key = arg.slice(2);
    if (!(key in filters)) {
      throw new Error(`Unsupported filter: ${arg}`);
    }
    const value = argv[i + 1];
    if (!value || value.startsWith('--')) {
      throw new Error(`Missing value for ${arg}`);
    }
    filters[key].push(value);
    i += 1;
  }
  return { filters, allowMissingDeps };
}

function matches(test, filters) {
  const kinds = filters.kind;
  const areas = filters.area;
  const speeds = filters.speed;
  const deps = filters.deps;
  if (kinds.length > 0 && !kinds.includes(test.kind)) {
    return false;
  }
  if (areas.length > 0 && !areas.includes(test.area)) {
    return false;
  }
  if (speeds.length > 0 && !speeds.includes(test.speed)) {
    return false;
  }
  if (deps.length > 0) {
    for (const dep of deps) {
      if (!test.deps.includes(dep)) {
        return false;
      }
    }
  }
  return true;
}

function runCommand(command, args, options = {}) {
  return new Promise((resolve) => {
    const child = spawn(command, args, { stdio: 'inherit', ...options });
    child.on('close', (code, signal) => {
      if (signal) {
        resolve({ ok: false, code: null, signal });
      } else {
        resolve({ ok: code === 0, code, signal: null });
      }
    });
  });
}

async function runNodeTest(test) {
  const absPath = path.join(ROOT, test.file);
  return runCommand(process.execPath, ['--test', absPath]);
}

async function runVitest(test) {
  if (!test.packageDir || !test.testFileInPackage) {
    throw new Error(`Missing package metadata for ${test.file}`);
  }
  const cwd = path.join(ROOT, test.packageDir);
  return runCommand('pnpm', ['vitest', 'run', test.testFileInPackage], { cwd });
}

async function runCargo(test) {
  if (!test.crateDir || !test.cargoTarget) {
    throw new Error(`Missing cargo metadata for ${test.file}`);
  }
  const cwd = path.join(ROOT, test.crateDir);
  return runCommand('cargo', ['test', '--test', test.cargoTarget], { cwd });
}

async function main() {
  const { filters, allowMissingDeps } = parseArgs(process.argv.slice(2));
  const tests = await discoverTests();
  const selected = tests.filter((test) => matches(test, filters));

  const summary = {
    ok: true,
    selected: selected.length,
    run: { node: 0, vitest: 0, cargo: 0 },
    skipped: [],
    results: [],
    filters,
    allowMissingDeps,
  };

  for (const test of selected) {
    if (allowMissingDeps && test.deps.includes('rust')) {
      summary.skipped.push({ file: test.file, reason: 'missing rust' });
      continue;
    }

    let result;
    if (test.runner === 'node') {
      result = await runNodeTest(test);
    } else if (test.runner === 'vitest') {
      result = await runVitest(test);
    } else if (test.runner === 'cargo') {
      result = await runCargo(test);
    } else {
      throw new Error(`Unknown runner for ${test.file}: ${test.runner}`);
    }

    summary.run[test.runner] += 1;
    summary.results.push({ file: test.file, runner: test.runner, ok: result.ok });
    if (!result.ok) {
      summary.ok = false;
    }
  }

  const outputDir = path.join(ROOT, 'out', '0.4', 'tests');
  await fs.mkdir(outputDir, { recursive: true });
  const outputPath = path.join(outputDir, 'manifest.json');
  await fs.writeFile(outputPath, `${JSON.stringify(summary, null, 2)}\n`);
  console.log(`Wrote ${path.relative(ROOT, outputPath)} (${summary.selected} selected, ${summary.results.length} executed)`);

  if (!summary.ok) {
    process.exitCode = 1;
  }
}

await main();
