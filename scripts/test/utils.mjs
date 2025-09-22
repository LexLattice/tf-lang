import { promises as fs } from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';

const ROOT = path.resolve(fileURLToPath(new URL('../../', import.meta.url)));
const IGNORE_DIRS = new Set(['.git', '.pnpm', 'node_modules', 'out', 'dist', 'build', 'tmp', 'temp', 'target']);
const TEST_SUFFIXES = ['.test.mjs', '.test.ts', '.spec.ts'];

function toPosix(relativePath) {
  return relativePath.split(path.sep).join('/');
}

function parseHeader(line) {
  const content = line.replace('//', '').trim();
  if (!content.startsWith('@tf-test')) {
    return null;
  }
  const rest = content.slice('@tf-test'.length).trim();
  if (!rest) {
    throw new Error('Missing metadata after @tf-test header');
  }
  return parseKeyValueString(rest);
}

function parseKeyValueString(str) {
  const result = {};
  for (const chunk of str.split(/\s+/)) {
    if (!chunk) continue;
    const [key, value] = chunk.split('=');
    if (!key || value === undefined) {
      throw new Error(`Invalid metadata chunk: ${chunk}`);
    }
    result[key] = value;
  }
  return result;
}

function parseMetaFile(content) {
  const result = {};
  for (const rawLine of content.split(/\r?\n/)) {
    const line = rawLine.trim();
    if (!line) continue;
    const [key, value] = line.split('=');
    if (!key || value === undefined) {
      throw new Error(`Invalid metadata line: ${line}`);
    }
    result[key] = value;
  }
  return result;
}

async function readFileHeaderMetadata(absPath) {
  const data = await fs.readFile(absPath, 'utf8');
  const [firstLine] = data.split(/\r?\n/, 1);
  if (!firstLine || !firstLine.startsWith('// @tf-test')) {
    throw new Error(`Missing @tf-test header in ${toPosix(path.relative(ROOT, absPath))}`);
  }
  const meta = parseHeader(firstLine);
  if (!meta) {
    throw new Error(`Unable to parse metadata for ${toPosix(path.relative(ROOT, absPath))}`);
  }
  return meta;
}

async function readMetaSidecar(absPath) {
  const content = await fs.readFile(absPath, 'utf8');
  return parseMetaFile(content);
}

function ensureFields(meta, filePath) {
  const required = ['kind', 'area', 'speed', 'deps'];
  for (const key of required) {
    if (!meta[key]) {
      throw new Error(`Missing ${key} metadata for ${filePath}`);
    }
  }
}

async function findNearestFile(start, fileName) {
  let current = start;
  while (true) {
    const candidate = path.join(current, fileName);
    try {
      await fs.access(candidate);
      return candidate;
    } catch (err) {
      const parent = path.dirname(current);
      if (parent === current) {
        return null;
      }
      current = parent;
    }
  }
}

export async function discoverTests() {
  const entries = [];

  async function walk(dir) {
    const dirents = await fs.readdir(dir, { withFileTypes: true });
    dirents.sort((a, b) => a.name.localeCompare(b.name));
    for (const dirent of dirents) {
      if (IGNORE_DIRS.has(dirent.name)) {
        continue;
      }
      const abs = path.join(dir, dirent.name);
      if (dirent.isDirectory()) {
        await walk(abs);
        continue;
      }
      if (dirent.isFile()) {
        const rel = toPosix(path.relative(ROOT, abs));
        if (rel.endsWith('.meta')) {
          const meta = await readMetaSidecar(abs);
          ensureFields(meta, rel);
          const targetRs = abs.slice(0, -'.meta'.length) + '.rs';
          const targetName = path.basename(targetRs, '.rs');
          const crateManifest = await findNearestFile(path.dirname(abs), 'Cargo.toml');
          const crateDir = crateManifest ? path.dirname(crateManifest) : null;
          entries.push({
            file: toPosix(path.relative(ROOT, targetRs)),
            metaFile: rel,
            kind: meta.kind,
            area: meta.area,
            speed: meta.speed,
            deps: meta.deps.split(',').map((value) => value.trim()).filter(Boolean),
            runner: 'cargo',
            crateDir: crateDir ? toPosix(path.relative(ROOT, crateDir)) : null,
            cargoTarget: targetName,
          });
          continue;
        }
        if (!TEST_SUFFIXES.some((suffix) => rel.endsWith(suffix))) {
          continue;
        }
        const meta = await readFileHeaderMetadata(abs);
        ensureFields(meta, rel);
        const deps = meta.deps.split(',').map((value) => value.trim()).filter(Boolean);
        let runner = 'node';
        let packageDir = null;
        let relativeTestFile = null;
        if (rel.endsWith('.test.ts') || rel.endsWith('.spec.ts')) {
          runner = 'vitest';
          const pkgPath = await findNearestFile(path.dirname(abs), 'package.json');
          if (!pkgPath) {
            throw new Error(`Unable to locate package.json for ${rel}`);
          }
          packageDir = toPosix(path.relative(ROOT, path.dirname(pkgPath)));
          relativeTestFile = toPosix(path.relative(path.dirname(pkgPath), abs));
        }
        entries.push({
          file: rel,
          kind: meta.kind,
          area: meta.area,
          speed: meta.speed,
          deps,
          runner,
          packageDir,
          testFileInPackage: relativeTestFile,
        });
      }
    }
  }

  await walk(ROOT);
  entries.sort((a, b) => a.file.localeCompare(b.file));
  return entries;
}

export { ROOT };
