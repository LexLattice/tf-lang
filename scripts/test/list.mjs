import { promises as fs } from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';

const __filename = fileURLToPath(import.meta.url);
const __dirname = path.dirname(__filename);
const ROOT = path.resolve(__dirname, '../..');
const IGNORED_DIRS = new Set(['.git', '.pnpm', '.turbo', 'node_modules', 'out', 'dist', 'target']);

function parseValue(key, value) {
  if (key === 'deps') {
    if (!value || value === 'none') return [];
    return value.split(',').map((part) => part.trim()).filter(Boolean);
  }
  return value;
}

function parseCommentMetadata(line, relPath) {
  const prefix = '// @tf-test ';
  if (!line.startsWith(prefix)) {
    throw new Error(`Missing metadata header in ${relPath}`);
  }
  const tokens = line.slice(prefix.length).trim().split(/\s+/);
  const meta = {};
  for (const token of tokens) {
    const [key, value] = token.split('=');
    if (!key || value === undefined) {
      throw new Error(`Invalid metadata token "${token}" in ${relPath}`);
    }
    meta[key] = parseValue(key, value);
  }
  if (!meta.deps) meta.deps = [];
  return meta;
}

function parseMetaFile(content, relPath) {
  const meta = {};
  for (const rawLine of content.split(/\r?\n/)) {
    const line = rawLine.trim();
    if (!line) continue;
    const [key, value] = line.split('=');
    if (!key || value === undefined) {
      throw new Error(`Invalid metadata entry "${line}" in ${relPath}`);
    }
    meta[key] = parseValue(key, value.trim());
  }
  if (!meta.deps) meta.deps = [];
  return meta;
}

async function fileExists(p) {
  try {
    await fs.access(p);
    return true;
  } catch {
    return false;
  }
}

async function findUp(startDir, target) {
  let current = startDir;
  while (true) {
    const candidate = path.join(current, target);
    if (await fileExists(candidate)) {
      return current;
    }
    const parent = path.dirname(current);
    if (parent === current) break;
    current = parent;
  }
  return null;
}

function isJsTest(name) {
  return /(\.test|\.spec)\.(mjs|cjs|js)$/u.test(name);
}

function isTsTest(name) {
  return /(\.test|\.spec)\.ts$/u.test(name);
}

export async function collectTests() {
  const tests = [];

  async function walk(dir) {
    const entries = await fs.readdir(dir, { withFileTypes: true });
    entries.sort((a, b) => a.name.localeCompare(b.name));
    for (const entry of entries) {
      if (IGNORED_DIRS.has(entry.name)) continue;
      const fullPath = path.join(dir, entry.name);
      const relPath = path.relative(ROOT, fullPath);
      if (entry.isDirectory()) {
        await walk(fullPath);
        continue;
      }
      if (isJsTest(entry.name) || isTsTest(entry.name)) {
        const content = await fs.readFile(fullPath, 'utf8');
        const firstLine = content.split(/\r?\n/, 1)[0] ?? '';
        const meta = parseCommentMetadata(firstLine, relPath);
        const runner = isTsTest(entry.name) ? 'vitest' : 'node';
        const record = {
          file: relPath,
          runner,
          meta,
        };
        if (runner === 'vitest') {
          const pkgDir = await findUp(path.dirname(fullPath), 'package.json');
          if (!pkgDir) {
            throw new Error(`Unable to locate package.json for ${relPath}`);
          }
          record.packageDir = pkgDir;
        }
        tests.push(record);
        continue;
      }
      if (entry.name.endsWith('.meta')) {
        const content = await fs.readFile(fullPath, 'utf8');
        const meta = parseMetaFile(content, relPath);
        let testFile = null;
        const base = fullPath.slice(0, -'.meta'.length);
        const candidates = ['.rs', '.sh'];
        for (const ext of candidates) {
          const candidatePath = base + ext;
          if (await fileExists(candidatePath)) {
            testFile = path.relative(ROOT, candidatePath);
            break;
          }
        }
        if (!testFile) {
          throw new Error(`Unable to find test file for metadata ${relPath}`);
        }
        const crateDir = await findUp(path.dirname(fullPath), 'Cargo.toml');
        if (!crateDir) {
          throw new Error(`Unable to locate Cargo.toml for ${relPath}`);
        }
        tests.push({
          file: testFile,
          runner: 'cargo',
          meta,
          crateDir,
          testTarget: path.basename(testFile, path.extname(testFile)),
        });
      }
    }
  }

  await walk(ROOT);
  tests.sort((a, b) => a.file.localeCompare(b.file));
  return tests;
}

async function writeAvailable(tests) {
  const outputDir = path.join(ROOT, 'out', '0.4', 'tests');
  await fs.mkdir(outputDir, { recursive: true });
  const records = tests.map((test) => {
    const entry = {
      file: test.file,
      runner: test.runner,
      kind: test.meta.kind,
      area: test.meta.area,
      speed: test.meta.speed,
      deps: test.meta.deps,
    };
    if (test.packageDir) {
      entry.package = path.relative(ROOT, test.packageDir);
    }
    if (test.crateDir) {
      entry.crate = path.relative(ROOT, test.crateDir);
    }
    return entry;
  });
  const payload = { tests: records };
  const serialized = `${JSON.stringify(payload, null, 2)}\n`;
  await fs.writeFile(path.join(outputDir, 'available.json'), serialized, 'utf8');
  return serialized;
}

async function main() {
  const tests = await collectTests();
  await writeAvailable(tests);
}

if (import.meta.url === `file://${process.argv[1]}`) {
  main().catch((err) => {
    console.error(err);
    process.exitCode = 1;
  });
}
