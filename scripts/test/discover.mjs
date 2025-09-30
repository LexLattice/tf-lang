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
  const tokens = source.trim().split(/\s+/).filter(Boolean);
  const meta = {};
  for (let i = 0; i < tokens.length; i += 1) {
    const token = tokens[i];
    const eqIndex = token.indexOf('=');
    if (eqIndex !== -1) {
      const key = token.slice(0, eqIndex);
      const value = token.slice(eqIndex + 1);
      if (!key || value.length === 0) {
        throw new Error(`Invalid metadata pair "${token}" in ${file}`);
      }
      meta[key] = value;
      continue;
    }
    if (token.endsWith(':')) {
      const key = token.slice(0, -1);
      const value = tokens[i + 1];
      if (!key || value === undefined) {
        throw new Error(`Invalid metadata pair "${token}" in ${file}`);
      }
      meta[key] = value;
      i += 1;
      continue;
    }
    throw new Error(`Invalid metadata token "${token}" in ${file}`);
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
  const required = ['kind', 'speed', 'deps'];
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

function parseHeaderMetadata(contents, file) {
  const trimmed = contents.trimStart();
  if (trimmed.startsWith('//')) {
    const [firstLine] = trimmed.split(/\r?\n/);
    const markerIndex = firstLine.indexOf('@tf-test');
    if (markerIndex === -1) {
      throw new Error(
        `Missing @tf-test header in ${file} (add: "@tf-test kind:<...> speed:<...> deps:<...>")`,
      );
    }
    const metaSource = firstLine.slice(markerIndex + '@tf-test'.length);
    return parseKeyValuePairs(metaSource, file);
  }
  if (trimmed.startsWith('/*')) {
    const endIndex = trimmed.indexOf('*/');
    if (endIndex === -1) {
      throw new Error(`Unterminated @tf-test block comment in ${file}`);
    }
    const inside = trimmed.slice(2, endIndex);
    const lines = inside
      .split(/\r?\n/)
      .map((line) => line.replace(/^\s*\*/u, '').trim())
      .filter((line) => line.length > 0);
    if (!lines.length) {
      throw new Error(
        `Missing @tf-test header in ${file} (add: "@tf-test kind:<...> speed:<...> deps:<...>")`,
      );
    }
    const markerIndex = lines.findIndex((line) => line.startsWith('@tf-test'));
    if (markerIndex === -1) {
      throw new Error(
        `Missing @tf-test header in ${file} (add: "@tf-test kind:<...> speed:<...> deps:<...>")`,
      );
    }
    const segments = [];
    const firstLine = lines[markerIndex];
    const remainder = firstLine.slice('@tf-test'.length).trim();
    if (remainder) {
      segments.push(remainder);
    }
    for (const line of lines.slice(markerIndex + 1)) {
      segments.push(line);
    }
    const metaSource = segments.join(' ');
    return parseKeyValuePairs(metaSource, file);
  }
  throw new Error(
    `Missing @tf-test header in ${file} (add: "@tf-test kind:<...> speed:<...> deps:<...>")`,
  );
}

async function parseJsTsTest(file) {
  const abs = path.join(ROOT, file);
  const contents = await readFile(abs, 'utf8');
  const lines = contents.split(/\r?\n/);
  const meta = parseHeaderMetadata(contents, file);
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
