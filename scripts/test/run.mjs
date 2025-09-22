#!/usr/bin/env node
import { promises as fs } from 'node:fs';
import path from 'node:path';
import { spawn, spawnSync } from 'node:child_process';
import { discoverTests } from './common.mjs';

const root = process.cwd();
const outDir = path.join(root, 'out', '0.4', 'tests');
const manifestPath = path.join(outDir, 'manifest.json');

const filters = { kind: [], area: [], speed: [], deps: [] };
let allowMissingDeps = false;
const availabilityCache = new Map();

parseArgs(process.argv.slice(2));

const tests = await discoverTests({ root });
const selected = tests.filter(test => matchesFilters(test, filters));

const runCounts = { node: 0, vitest: 0, cargo: 0 };
const skipped = [];
const failures = [];
let ok = true;

if (!selected.length) {
  console.log('No tests selected.');
}

for (const test of selected) {
  const missing = missingDependencies(test);
  if (missing.length) {
    const reason = `missing ${missing.join(', ')}`;
    if (allowMissingDeps) {
      skipped.push({ file: test.file, reason });
      continue;
    }
    ok = false;
    failures.push({ file: test.file, reason });
    console.error(`Cannot run ${test.file}: ${reason}`);
    break;
  }

  const success = await runTest(test);
  if (!success) {
    ok = false;
    failures.push({ file: test.file, reason: 'command failed' });
    break;
  }
}

await fs.mkdir(outDir, { recursive: true });
const manifest = {
  ok,
  selected: selected.length,
  run: runCounts,
  skipped,
};
if (failures.length) {
  manifest.failures = failures;
}
await fs.writeFile(manifestPath, JSON.stringify(manifest, null, 2) + '\n');

if (!ok) {
  process.exitCode = 1;
}

function parseArgs(args) {
  for (let i = 0; i < args.length; i += 1) {
    const arg = args[i];
    if (arg === '--allow-missing-deps') {
      allowMissingDeps = true;
      continue;
    }
    if (arg === '--help') {
      printHelp();
      process.exit(0);
    }
    if (!arg.startsWith('--')) {
      throw new Error(`Unexpected argument: ${arg}`);
    }
    const key = arg.slice(2);
    if (!(key in filters)) {
      throw new Error(`Unknown filter: ${key}`);
    }
    const value = args[i + 1];
    if (!value) {
      throw new Error(`Missing value for --${key}`);
    }
    filters[key].push(value);
    i += 1;
  }
}

function printHelp() {
  console.log('Usage: node scripts/test/run.mjs [filters]');
  console.log('Filters: --kind <value>, --area <value>, --speed <value>, --deps <value>');
  console.log('Options: --allow-missing-deps');
}

function matchesFilters(test, { kind, area, speed, deps }) {
  if (kind.length && !kind.includes(test.kind)) return false;
  if (area.length && !area.includes(test.area)) return false;
  if (speed.length && !speed.includes(test.speed)) return false;
  if (deps.length && !deps.every(dep => test.deps.includes(dep))) return false;
  return true;
}

function missingDependencies(test) {
  const missing = [];
  for (const dep of test.deps) {
    if (!hasDependency(dep)) {
      missing.push(dep);
    }
  }
  return missing;
}

function hasDependency(dep) {
  if (availabilityCache.has(dep)) {
    return availabilityCache.get(dep);
  }
  let available = true;
  if (dep === 'node') {
    available = true;
  } else if (dep === 'rust') {
    try {
      const result = spawnSync('cargo', ['--version'], { stdio: 'ignore' });
      available = result.status === 0;
    } catch (err) {
      available = false;
    }
  }
  availabilityCache.set(dep, available);
  return available;
}

async function runTest(test) {
  console.log(`[${test.runner}] ${test.file}`);
  if (test.runner === 'node') {
    runCounts.node += 1;
    return runCommand(process.execPath, ['--test', test.file], { cwd: root });
  }
  if (test.runner === 'vitest') {
    const pkgDir = await findPackageRoot(path.join(root, test.file));
    const pkgRelative = path.relative(root, pkgDir) || '.';
    const relTest = path.relative(pkgDir, path.join(root, test.file));
    const args = ['--dir', pkgDir, 'exec', 'vitest', 'run', relTest];
    runCounts.vitest += 1;
    return runCommand('pnpm', args, { cwd: root });
  }
  if (test.runner === 'cargo') {
    const crateDir = await findCargoRoot(path.join(root, test.file));
    const manifest = path.join(crateDir, 'Cargo.toml');
    const testName = path.basename(test.file).replace(/\.[^.]+$/, '');
    const args = ['test', '--manifest-path', manifest, '--test', testName];
    runCounts.cargo += 1;
    return runCommand('cargo', args, { cwd: root });
  }
  throw new Error(`Unknown runner: ${test.runner}`);
}

async function findPackageRoot(startPath) {
  let dir = await fs.realpath(path.dirname(startPath));
  const rootReal = await fs.realpath(root);
  while (dir.startsWith(rootReal)) {
    const pkgPath = path.join(dir, 'package.json');
    if (await exists(pkgPath)) {
      return dir;
    }
    const parent = path.dirname(dir);
    if (parent === dir) break;
    dir = parent;
  }
  throw new Error(`Unable to locate package.json for ${startPath}`);
}

async function findCargoRoot(startPath) {
  let dir = await fs.realpath(path.dirname(startPath));
  const rootReal = await fs.realpath(root);
  while (dir.startsWith(rootReal)) {
    const manifest = path.join(dir, 'Cargo.toml');
    if (await exists(manifest)) {
      return dir;
    }
    const parent = path.dirname(dir);
    if (parent === dir) break;
    dir = parent;
  }
  throw new Error(`Unable to locate Cargo.toml for ${startPath}`);
}

async function exists(filePath) {
  try {
    await fs.access(filePath);
    return true;
  } catch (err) {
    if (err && err.code === 'ENOENT') return false;
    throw err;
  }
}

function runCommand(cmd, args, { cwd }) {
  return new Promise(resolve => {
    const child = spawn(cmd, args, { cwd, stdio: 'inherit' });
    child.on('exit', code => {
      resolve(typeof code === 'number' && code === 0);
    });
    child.on('error', () => resolve(false));
  });
}
