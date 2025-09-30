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

function parseKeyValueSegments(source, file) {
  const meta = {};
  const lines = source.split(/\r?\n/);
  for (const rawLine of lines) {
    let line = rawLine.trim();
    if (!line) continue;
    while (line.length > 0) {
      const match = line.match(/^([A-Za-z0-9_-]+)\s*[:=]\s*(.*)$/u);
      if (!match) {
        throw new Error(`Invalid metadata token "${line}" in ${file}`);
      }
      const [, key, remainder] = match;
      if (!remainder || remainder.trim().length === 0) {
        throw new Error(`Missing value for ${key} in ${file}`);
      }
      const nextKeyIndex = remainder.search(/\s+[A-Za-z0-9_-]+\s*[:=]/u);
      if (nextKeyIndex === -1) {
        meta[key] = remainder.trim();
        line = '';
      } else {
        const value = remainder.slice(0, nextKeyIndex).trim();
        if (!value) {
          throw new Error(`Missing value for ${key} in ${file}`);
        }
        meta[key] = value;
        line = remainder.slice(nextKeyIndex).trim();
      }
    }
  }
  return meta;
}

function parseMetaLines(lines, file) {
  return parseKeyValueSegments(lines.join('\n'), file);
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
    area: meta.area ?? 'misc',
    speed: meta.speed,
    deps: normalizeDeps(meta.deps),
  };
}

function extractLeadingComment(contents, file) {
  let index = 0;
  if (contents.startsWith('#!')) {
    const newlineIndex = contents.indexOf('\n');
    if (newlineIndex === -1) {
      return null;
    }
    index = newlineIndex + 1;
  }
  while (index < contents.length) {
    const char = contents[index];
    if (/\s/u.test(char)) {
      index += 1;
      continue;
    }
    if (char === '/' && contents[index + 1] === '/') {
      const lines = [];
      while (index < contents.length && contents[index] === '/' && contents[index + 1] === '/') {
        let lineStart = index + 2;
        let lineEnd = lineStart;
        while (lineEnd < contents.length && contents[lineEnd] !== '\n' && contents[lineEnd] !== '\r') {
          lineEnd += 1;
        }
        lines.push(contents.slice(lineStart, lineEnd));
        index = lineEnd;
        if (contents[index] === '\r') index += 1;
        if (contents[index] === '\n') index += 1;
      }
      return { type: 'line', text: lines.join('\n') };
    }
    if (char === '/' && contents[index + 1] === '*') {
      const endIndex = contents.indexOf('*/', index + 2);
      if (endIndex === -1) {
        throw new Error(`Unterminated block comment in ${file}`);
      }
      const inside = contents.slice(index + 2, endIndex);
      return { type: 'block', text: inside };
    }
    break;
  }
  return null;
}

function parseHeaderMetadata(contents, file) {
  const comment = extractLeadingComment(contents, file);
  if (!comment) {
    throw new Error(`Missing @tf-test header in ${file}`);
  }
  let text = comment.text;
  if (comment.type === 'block') {
    text = text
      .split(/\r?\n/)
      .map((line) => line.replace(/^\s*\*/u, '').trim())
      .join('\n');
  }
  const markerIndex = text.indexOf('@tf-test');
  if (markerIndex === -1) {
    throw new Error(`Missing @tf-test header in ${file}`);
  }
  const metaSource = text.slice(markerIndex + '@tf-test'.length);
  return parseKeyValueSegments(metaSource, file);
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
