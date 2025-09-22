import { promises as fs } from 'node:fs';
import path from 'node:path';

const TEST_EXTENSIONS = new Set(['.test.mjs', '.test.js', '.test.ts', '.spec.ts']);
const IGNORE_DIRS = new Set([
  '.git',
  'node_modules',
  'out',
  'dist',
  'build',
  'target',
  '.pnpm',
  '.pnpm-store',
  '.turbo',
]);

function parseKeyValueLine(line) {
  const data = {};
  const parts = line.trim().split(/\s+/);
  for (const part of parts) {
    if (!part) continue;
    const eq = part.indexOf('=');
    if (eq === -1) continue;
    const key = part.slice(0, eq);
    const value = part.slice(eq + 1);
    data[key] = value;
  }
  return data;
}

function parseMetaContent(content) {
  const data = {};
  for (const rawLine of content.split(/\r?\n/)) {
    const line = rawLine.trim();
    if (!line || line.startsWith('#')) continue;
    const eq = line.indexOf('=');
    if (eq === -1) continue;
    const key = line.slice(0, eq);
    const value = line.slice(eq + 1);
    data[key] = value;
  }
  return data;
}

function normalizeDeps(value) {
  if (!value) return [];
  return value
    .split(',')
    .map(dep => dep.trim())
    .filter(Boolean);
}

function normalizeEntry({ file, runner, meta, source, sidecar }) {
  const { kind, area, speed, deps } = meta;
  return {
    file,
    runner,
    kind,
    area,
    speed,
    deps: normalizeDeps(deps),
    source,
    sidecar,
  };
}

async function readHeaderMeta(filePath) {
  const data = await fs.readFile(filePath, 'utf8');
  const firstLine = data.split(/\r?\n/, 1)[0] ?? '';
  const match = firstLine.match(/^\/\/\s*@tf-test\s+(.*)$/);
  if (!match) {
    throw new Error(`Missing @tf-test header in ${filePath}`);
  }
  return parseKeyValueLine(match[1]);
}

async function discoverFromDirectory(dir, results) {
  const entries = await fs.readdir(dir, { withFileTypes: true });
  for (const entry of entries) {
    const entryPath = path.join(dir, entry.name);
    if (entry.isDirectory()) {
      if (IGNORE_DIRS.has(entry.name)) continue;
      await discoverFromDirectory(entryPath, results);
      continue;
    }
    if (entry.isFile()) {
      if (entry.name.endsWith('.meta')) {
        results.metaFiles.push(entryPath);
        continue;
      }
      for (const ext of TEST_EXTENSIONS) {
        if (entry.name.endsWith(ext)) {
          results.testFiles.push(entryPath);
          break;
        }
      }
    }
  }
}

export async function discoverTests({ root = process.cwd() } = {}) {
  const results = { testFiles: [], metaFiles: [] };
  await discoverFromDirectory(root, results);

  const entries = [];
  for (const absolute of results.testFiles) {
    const meta = await readHeaderMeta(absolute);
    const relative = path.relative(root, absolute);
    const ext = path.extname(absolute);
    const runner = ext === '.mjs' || ext === '.js' ? 'node' : 'vitest';
    entries.push(
      normalizeEntry({
        file: relative,
        runner,
        meta,
        source: 'header',
      })
    );
  }

  for (const metaPath of results.metaFiles) {
    const meta = parseMetaContent(await fs.readFile(metaPath, 'utf8'));
    const base = metaPath.slice(0, -'.meta'.length);
    const rsPath = base.endsWith('.rs') ? base : `${base}.rs`;
    const absolute = rsPath;
    if (!(await fileExists(absolute))) {
      continue;
    }
    const relative = path.relative(root, absolute);
    entries.push(
      normalizeEntry({
        file: relative,
        runner: 'cargo',
        meta,
        source: 'sidecar',
        sidecar: path.relative(root, metaPath),
      })
    );
  }

  entries.sort((a, b) => a.file.localeCompare(b.file));
  return entries;
}

async function fileExists(filePath) {
  try {
    await fs.access(filePath);
    return true;
  } catch (err) {
    if (err && err.code === 'ENOENT') return false;
    throw err;
  }
}
