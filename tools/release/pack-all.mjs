#!/usr/bin/env node
import { execSync } from 'node:child_process';
import { createHash } from 'node:crypto';
import { promises as fs } from 'node:fs';
import { mkdtempSync, rmSync } from 'node:fs';
import { tmpdir } from 'node:os';
import path from 'node:path';

const ROOT = process.cwd();
const OUTPUT_PATH = path.join(ROOT, 'out/0.5/release/pack.json');
const IGNORED_DIRS = new Set(['.git', 'node_modules', 'out', 'dist', '.pnpm']);
const DEFAULT_ROOTS = [
  '.',
  'packages',
  'clients',
  'services',
  'tools',
  'scripts',
  'crates',
  'schemas',
  'templates',
  'examples',
  'tasks',
];

function parseArgs(argv) {
  const options = { json: false, quiet: false };
  for (const arg of argv) {
    if (arg === '--json') {
      options.json = true;
      continue;
    }
    if (arg === '--quiet') {
      options.quiet = true;
      continue;
    }
    console.error(`Unknown flag: ${arg}`);
    process.exit(1);
  }
  return options;
}

function emit(payload, { quiet, json }) {
  if (!quiet) {
    const output = JSON.stringify(payload);
    process.stdout.write(`${json ? output : output}\n`);
  }
}

function getRootAllowlist() {
  const raw = process.env.PACK_ROOTS;
  if (!raw) {
    return { roots: DEFAULT_ROOTS, allowRootTraversal: false };
  }
  const roots = raw
    .split(/[,:]/)
    .map((item) => item.trim())
    .filter(Boolean);
  const allowRootTraversal = roots.includes('.');
  return { roots, allowRootTraversal };
}

async function walkForPackages(dir) {
  const entries = await fs.readdir(dir, { withFileTypes: true });
  const packages = [];

  for (const entry of entries) {
    const entryPath = path.join(dir, entry.name);

    if (entry.isDirectory()) {
      if (IGNORED_DIRS.has(entry.name)) {
        continue;
      }
      packages.push(...(await walkForPackages(entryPath)));
      continue;
    }

    if (entry.isFile() && entry.name === 'package.json') {
      packages.push(entryPath);
    }
  }

  return packages;
}

async function readManifest(manifestPath) {
  try {
    const raw = await fs.readFile(manifestPath, 'utf8');
    return JSON.parse(raw);
  } catch (error) {
    return null;
  }
}

function ensureDir(dir) {
  return fs.mkdir(dir, { recursive: true });
}

function runPack(manifestPath, tmpDir) {
  const cwd = path.dirname(manifestPath);
  const cmd = `pnpm pack --json --pack-destination ${JSON.stringify(tmpDir)}`;
  const raw = execSync(cmd, { cwd, encoding: 'utf8' }).trim();
  if (!raw) {
    return [];
  }

  try {
    let payload = raw;
    if (!payload.startsWith('{') && !payload.startsWith('[')) {
      const brace = payload.indexOf('{');
      const bracket = payload.indexOf('[');
      const startCandidates = [brace, bracket].filter((idx) => idx >= 0);
      if (startCandidates.length === 0) {
        throw new Error(`No JSON payload found in pack output: ${payload}`);
      }
      const start = Math.min(...startCandidates);
      payload = payload.slice(start).trim();
    }

    const parsed = JSON.parse(payload);
    return Array.isArray(parsed) ? parsed : [parsed];
  } catch (error) {
    const lines = raw.split(/\r?\n/).filter(Boolean);
    return lines.map((line) => JSON.parse(line));
  }
}

async function discoverManifestPaths(allowlist, { allowRootTraversal }) {
  const manifests = new Set();

  // Root manifest (if any) should always be evaluated.
  const rootManifest = path.join(ROOT, 'package.json');
  try {
    const stat = await fs.stat(rootManifest);
    if (stat.isFile()) {
      manifests.add(rootManifest);
    }
  } catch (_) {
    // noop
  }

  for (const rel of allowlist) {
    if (!rel) {
      continue;
    }
    if (rel === '.') {
      if (allowRootTraversal) {
        const discovered = await walkForPackages(ROOT);
        for (const manifestPath of discovered) {
          manifests.add(manifestPath);
        }
      }
      continue;
    }
    const abs = path.resolve(ROOT, rel);
    if (!abs.startsWith(ROOT)) {
      continue;
    }
    try {
      const stat = await fs.stat(abs);
      if (!stat.isDirectory()) {
        continue;
      }
    } catch (_) {
      continue;
    }
    const discovered = await walkForPackages(abs);
    for (const manifestPath of discovered) {
      manifests.add(manifestPath);
    }
  }

  return Array.from(manifests);
}

function sortPackages(packages) {
  return packages.sort((a, b) => {
    const nameA = a.manifest.name || a.directory;
    const nameB = b.manifest.name || b.directory;
    return nameA.localeCompare(nameB);
  });
}

async function main(options) {
  const tmpDir = mkdtempSync(path.join(tmpdir(), 'tf-pack-'));
  const packages = [];

  try {
    const { roots: allowlist, allowRootTraversal } = getRootAllowlist();
    const manifestPaths = await discoverManifestPaths(allowlist, {
      allowRootTraversal,
    });
    for (const manifestPath of manifestPaths.sort()) {
      const manifest = await readManifest(manifestPath);
      if (!manifest || manifest.private === true) {
        continue;
      }

      const packInfo = runPack(manifestPath, tmpDir);
      const relativeDir = path.relative(ROOT, path.dirname(manifestPath)) || '.';

      packages.push({
        directory: relativeDir,
        manifest: {
          name: manifest.name || null,
          version: manifest.version || null,
          path: path.relative(ROOT, manifestPath),
        },
        artifacts: packInfo.map((entry) => ({
          filename: entry.filename,
          size: entry.size ?? null,
          integrity: entry.integrity ?? null,
          shasum: entry.shasum ?? null,
        })),
      });
    }

    const sorted = sortPackages(packages);
    const payload = {
      ok: true,
      generated_at: new Date().toISOString(),
      packages: sorted,
      allowed_roots: allowlist,
      allow_root_traversal: allowRootTraversal,
    };

    await ensureDir(path.dirname(OUTPUT_PATH));
    const serialized = `${JSON.stringify(payload, null, 2)}\n`;
    await fs.writeFile(OUTPUT_PATH, serialized, 'utf8');

    const checksum = createHash('sha256').update(serialized).digest('hex');
    emit(
      {
        ok: true,
        output: path.relative(ROOT, OUTPUT_PATH),
        checksum,
        packages: sorted.length,
      },
      options,
    );
  } finally {
    rmSync(tmpDir, { recursive: true, force: true });
  }
}

const options = parseArgs(process.argv.slice(2));

main(options).catch((error) => {
  if (error.stdout) {
    const stdout = error.stdout.toString().trim();
    if (stdout) {
      console.error(stdout);
    }
  }
  if (error.stderr) {
    const stderr = error.stderr.toString().trim();
    if (stderr) {
      console.error(stderr);
    }
  }
  console.error(`pack-all failed: ${error.message}`);
  emit({ ok: false, error: error.message }, options);
  process.exit(1);
});
