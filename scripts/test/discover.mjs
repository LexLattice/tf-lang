import { readdir, readFile } from 'node:fs/promises';
import path from 'node:path';
import { fileURLToPath } from 'node:url';

import { sortTests } from './utils.mjs';

const ROOT = path.resolve(fileURLToPath(new URL('../../', import.meta.url)));
const IGNORE_DIRS = new Set(['.git', 'node_modules', 'out', 'dist', 'build', '.pnpm', 'target']);
const TEST_EXTENSIONS = new Set(['.mjs', '.js', '.ts']);

function toPosix(p) {
  return p.split(path.sep).join('/');
}

async function walk(dir, results) {
  const entries = await readdir(dir, { withFileTypes: true });
  entries.sort((a, b) => a.name.localeCompare(b.name));
  for (const entry of entries) {
    if (entry.isSymbolicLink()) continue;
    if (entry.isDirectory()) {
      if (IGNORE_DIRS.has(entry.name)) continue;
      await walk(path.join(dir, entry.name), results);
    } else if (entry.isFile()) {
      const rel = toPosix(path.relative(ROOT, path.join(dir, entry.name)));
      results.push(rel);
    }
  }
}

function parseKeyValuePairs(source, file) {
  const pairs = source.trim().split(/\s+/).filter(Boolean);
  const meta = {};
  for (const pair of pairs) {
    const [key, value] = pair.split('=');
    if (!key || value === undefined) {
      throw new Error(`Invalid metadata pair "${pair}" in ${file}`);
    }
    meta[key] = value;
  }
  return meta;
}

function parseMetaLines(lines, file) {
  const meta = {};
  for (const line of lines) {
    const trimmed = line.trim();
    if (!trimmed) continue;
    const [key, value] = trimmed.split('=');
    if (!key || value === undefined) {
      throw new Error(`Invalid metadata line "${line}" in ${file}`);
    }
    meta[key] = value;
  }
  return meta;
}

function normalizeDeps(value) {
  if (!value) return [];
  const deps = value.split(',').map((dep) => dep.trim()).filter(Boolean);
  if (deps.length === 1 && deps[0].toLowerCase() === 'none') {
    return [];
  }
  return deps.sort((a, b) => a.localeCompare(b));
}

function ensureMetadata(meta, file) {
  const required = ['kind', 'area', 'speed', 'deps'];
  for (const key of required) {
    if (!meta[key]) {
      throw new Error(`Missing ${key} metadata in ${file}`);
    }
  }
  return {
    kind: meta.kind,
    area: meta.area,
    speed: meta.speed,
    deps: normalizeDeps(meta.deps),
  };
}

async function parseJsTsTest(file) {
  const abs = path.join(ROOT, file);
  const contents = await readFile(abs, 'utf8');
  const lines = contents.split(/\r?\n/);
  const header = lines.find((line) => line.trim() !== '');
  if (!header || !header.trim().startsWith('// @tf-test ')) {
    throw new Error(`Missing @tf-test header in ${file}`);
  }
  const meta = parseKeyValuePairs(header.trim().slice('// @tf-test '.length), file);
  const baseMeta = ensureMetadata(meta, file);
  const ext = path.extname(file);
  if (ext === '.mjs' || ext === '.js') {
    return {
      file,
      ...baseMeta,
      runner: {
        type: 'node',
        command: ['node', '--test', file],
        cwd: '.',
      },
    };
  }
  if (ext === '.ts') {
    const pkgDir = await findPackageDir(path.dirname(file));
    const relTest = toPosix(path.relative(pkgDir, path.join(ROOT, file)));
    return {
      file,
      ...baseMeta,
      runner: {
        type: 'vitest',
        command: ['pnpm', '-C', toPosix(path.relative(ROOT, pkgDir)), 'vitest', 'run', relTest],
        cwd: '.',
        packageDir: toPosix(path.relative(ROOT, pkgDir)),
        testPath: relTest,
      },
    };
  }
  throw new Error(`Unsupported test extension for ${file}`);
}

async function findPackageDir(startRel) {
  let current = path.join(ROOT, startRel);
  while (true) {
    const candidate = path.join(current, 'package.json');
    try {
      await readFile(candidate);
      return current;
    } catch (err) {
      const parent = path.dirname(current);
      if (parent === current || parent.length < ROOT.length) {
        throw new Error(`Unable to find package.json for ${startRel}`);
      }
      current = parent;
    }
  }
}

async function parseMetaTest(file) {
  const absMeta = path.join(ROOT, file);
  const contents = await readFile(absMeta, 'utf8');
  const meta = parseMetaLines(contents.split(/\r?\n/), file);
  const baseMeta = ensureMetadata(meta, file);
  const testFile = file.replace(/\.meta$/u, '.rs');
  const manifestDir = await findCargoDir(path.dirname(file));
  const manifestRel = toPosix(path.relative(ROOT, path.join(manifestDir, 'Cargo.toml')));
  const testName = path.basename(testFile, '.rs');
  return {
    file: toPosix(testFile),
    metaFile: file,
    ...baseMeta,
    runner: {
      type: 'cargo',
      command: ['cargo', 'test', '--manifest-path', manifestRel, '--test', testName],
      cwd: '.',
      manifestPath: manifestRel,
      testName,
    },
  };
}

async function findCargoDir(startRel) {
  let current = path.join(ROOT, startRel);
  while (true) {
    const candidate = path.join(current, 'Cargo.toml');
    try {
      await readFile(candidate);
      return current;
    } catch (err) {
      const parent = path.dirname(current);
      if (parent === current || parent.length < ROOT.length) {
        throw new Error(`Unable to find Cargo.toml for ${startRel}`);
      }
      current = parent;
    }
  }
}

export async function discoverTests() {
  const files = [];
  await walk(ROOT, files);
  files.sort();
  const tests = [];
  for (const file of files) {
    if (file.endsWith('.meta')) {
      tests.push(await parseMetaTest(file));
      continue;
    }
    const ext = path.extname(file);
    if (!TEST_EXTENSIONS.has(ext)) continue;
    if (!file.endsWith('.test' + ext)) continue;
    tests.push(await parseJsTsTest(file));
  }
  return sortTests(tests);
}
