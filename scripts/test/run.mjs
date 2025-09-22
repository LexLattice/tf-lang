import { promises as fs } from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { spawn } from 'node:child_process';

import { collectTests } from './list.mjs';

const __filename = fileURLToPath(import.meta.url);
const __dirname = path.dirname(__filename);
const ROOT = path.resolve(__dirname, '../..');

function parseArgs(argv) {
  const filters = new Map();
  let allowMissingDeps = false;
  for (let i = 0; i < argv.length; i += 1) {
    const arg = argv[i];
    if (arg === '--allow-missing-deps') {
      allowMissingDeps = true;
      continue;
    }
    if (!arg.startsWith('--')) {
      throw new Error(`Unexpected argument "${arg}"`);
    }
    const key = arg.slice(2);
    const value = argv[i + 1];
    if (value === undefined || value.startsWith('--')) {
      throw new Error(`Missing value for argument "${arg}"`);
    }
    i += 1;
    if (!filters.has(key)) {
      filters.set(key, []);
    }
    filters.get(key).push(value);
  }
  return { filters, allowMissingDeps };
}

function matchesFilters(test, filters) {
  for (const [key, values] of filters) {
    if (key === 'deps') {
      const deps = test.meta.deps ?? [];
      if (!values.every((value) => deps.includes(value))) {
        return false;
      }
      continue;
    }
    const metaValue = test.meta[key];
    if (!values.includes(metaValue)) {
      return false;
    }
  }
  return true;
}

function runCommand(command, args, { cwd = ROOT, env } = {}) {
  return new Promise((resolve, reject) => {
    const child = spawn(command, args, {
      cwd,
      env: env ? { ...process.env, ...env } : process.env,
      stdio: 'inherit',
    });
    child.on('error', reject);
    child.on('close', (code, signal) => {
      if (signal) {
        resolve(1);
      } else {
        resolve(code ?? 0);
      }
    });
  });
}

function commandExists(command, args) {
  return new Promise((resolve) => {
    const child = spawn(command, args, { stdio: 'ignore' });
    child.on('error', () => resolve(false));
    child.on('close', (code) => resolve(code === 0));
  });
}

async function detectMissingDeps(tests) {
  const required = new Set();
  for (const test of tests) {
    for (const dep of test.meta.deps ?? []) {
      required.add(dep);
    }
  }
  const missing = new Set();
  for (const dep of required) {
    if (dep === 'none' || dep === 'node') continue;
    if (dep === 'rust') {
      const available = await commandExists('cargo', ['--version']);
      if (!available) missing.add(dep);
      continue;
    }
    // Assume other deps are available for now.
  }
  return missing;
}

async function runNodeTests(tests) {
  if (tests.length === 0) return 0;
  const args = ['--test', ...tests.map((test) => test.file)];
  const code = await runCommand(process.execPath, args);
  return code === 0 ? 0 : 1;
}

async function runVitestTests(tests) {
  if (tests.length === 0) return 0;
  let failures = 0;
  const byPackage = new Map();
  for (const test of tests) {
    const pkgDir = test.packageDir;
    if (!pkgDir) {
      throw new Error(`Missing package directory for ${test.file}`);
    }
    if (!byPackage.has(pkgDir)) {
      byPackage.set(pkgDir, []);
    }
    byPackage.get(pkgDir).push(test);
  }
  for (const [pkgDir, groupedTests] of byPackage) {
    const relPaths = groupedTests.map((test) => {
      const absolute = path.join(ROOT, test.file);
      return path.relative(pkgDir, absolute);
    });
    const code = await runCommand('pnpm', ['exec', 'vitest', 'run', ...relPaths], { cwd: pkgDir });
    if (code !== 0) {
      failures += 1;
    }
  }
  return failures;
}

async function runCargoTests(tests) {
  if (tests.length === 0) return 0;
  let failures = 0;
  for (const test of tests) {
    const crateDir = test.crateDir;
    const manifest = path.join(crateDir, 'Cargo.toml');
    const args = ['test', '--manifest-path', manifest, '--test', test.testTarget];
    const code = await runCommand('cargo', args, { cwd: crateDir });
    if (code !== 0) {
      failures += 1;
    }
  }
  return failures;
}

async function main() {
  const { filters, allowMissingDeps } = parseArgs(process.argv.slice(2));
  const tests = await collectTests();
  const selected = filters.size === 0 ? tests : tests.filter((test) => matchesFilters(test, filters));
  const manifest = {
    ok: true,
    selected: selected.length,
    run: { node: 0, vitest: 0, cargo: 0 },
    skipped: [],
  };

  const missingDeps = await detectMissingDeps(selected);
  const runnable = [];
  for (const test of selected) {
    const missingForTest = (test.meta.deps ?? []).filter((dep) => missingDeps.has(dep));
    if (missingForTest.length > 0) {
      const reason = `missing ${missingForTest.join(', ')}`;
      manifest.skipped.push({ file: test.file, reason });
      if (!allowMissingDeps) {
        manifest.ok = false;
      }
      if (!allowMissingDeps) {
        console.error(`Cannot run ${test.file}: ${reason}`);
      } else {
        console.warn(`Skipping ${test.file}: ${reason}`);
      }
      continue;
    }
    runnable.push(test);
  }

  const nodeTests = runnable.filter((test) => test.runner === 'node');
  if (nodeTests.length > 0) {
    const failures = await runNodeTests(nodeTests);
    manifest.run.node = nodeTests.length;
    if (failures > 0) manifest.ok = false;
  }

  const vitestTests = runnable.filter((test) => test.runner === 'vitest');
  if (vitestTests.length > 0) {
    const failures = await runVitestTests(vitestTests);
    manifest.run.vitest = vitestTests.length;
    if (failures > 0) manifest.ok = false;
  }

  const cargoTests = runnable.filter((test) => test.runner === 'cargo');
  if (cargoTests.length > 0) {
    const failures = await runCargoTests(cargoTests);
    manifest.run.cargo = cargoTests.length;
    if (failures > 0) manifest.ok = false;
  }

  const outputDir = path.join(ROOT, 'out', '0.4', 'tests');
  await fs.mkdir(outputDir, { recursive: true });
  const serialized = `${JSON.stringify(manifest, null, 2)}\n`;
  await fs.writeFile(path.join(outputDir, 'manifest.json'), serialized, 'utf8');

  if (!manifest.ok) {
    process.exitCode = 1;
  }
}

main().catch((err) => {
  console.error(err);
  process.exitCode = 1;
});
