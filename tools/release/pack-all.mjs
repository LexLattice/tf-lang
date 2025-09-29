#!/usr/bin/env node
import { execSync } from 'node:child_process';
import { createHash } from 'node:crypto';
import { promises as fs } from 'node:fs';
import { mkdtempSync, rmSync } from 'node:fs';
import { tmpdir } from 'node:os';
import path from 'node:path';

import { emitJson, logStep, parseArgs, UsageError } from './_shared.mjs';

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

function runPack(manifestPath, tmpDir, { dryRun }) {
  const cwd = path.dirname(manifestPath);
  if (dryRun) {
    logStep(`dry-run: skipping pack for ${path.relative(ROOT, manifestPath)}`);
    return [];
  }
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

async function buildPack(args) {
  const tmpDir = mkdtempSync(path.join(tmpdir(), 'tf-pack-'));
  const packages = [];

  try {
    const { roots: allowlist, allowRootTraversal } = getRootAllowlist();
    logStep(`allowlist roots: ${allowlist.join(', ')}`);
    const manifestPaths = await discoverManifestPaths(allowlist, {
      allowRootTraversal,
    });
    logStep(`discovered ${manifestPaths.length} manifests`);
    for (const manifestPath of manifestPaths.sort()) {
      const manifest = await readManifest(manifestPath);
      if (!manifest || manifest.private === true) {
        continue;
      }

      const packInfo = runPack(manifestPath, tmpDir, args);
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
    const statusBody = await emitJson(
      {
        ok: true,
        output: path.relative(ROOT, OUTPUT_PATH),
        checksum,
        packages: sorted.length,
      },
      args.out,
    );
    if (!args.quiet) {
      process.stdout.write(statusBody);
    }
  } finally {
    rmSync(tmpDir, { recursive: true, force: true });
  }
}

async function main(argv) {
  const args = parseArgs(argv, {
    usage: 'node tools/release/pack-all.mjs [options]',
    description: 'Generate the release pack manifest for all public packages.',
    flags: {
      out: {
        description: 'Write the JSON status output to this path in addition to stdout.',
      },
      dryRun: {
        description: 'Skip running pnpm pack and just enumerate manifests.',
      },
      tag: false,
      range: false,
      verbose: {
        description: 'Emit progress information to stderr.',
      },
      quiet: {
        description: 'Suppress stdout emission of the JSON status.',
      },
    },
  });

  if (args.help) {
    process.stdout.write(args.helpText);
    return args;
  }

  if (args.verbose) {
    process.env.RELEASE_VERBOSE = '1';
  }

  await buildPack(args);
  return args;
}

async function run() {
  let args;
  try {
    args = await main(process.argv.slice(2));
  } catch (error) {
    if (error instanceof UsageError) {
      if (error.message) {
        console.error(error.message);
      }
      if (error.helpText) {
        process.stderr.write(error.helpText);
      }
      process.exit(error.exitCode);
    }
    if (error && typeof error === 'object') {
      const stdout = error.stdout?.toString().trim();
      const stderr = error.stderr?.toString().trim();
      if (stdout) {
        console.error(stdout);
      }
      if (stderr) {
        console.error(stderr);
      }
    }
    console.error(`pack-all failed: ${error.message}`);
    if (args) {
      const failureBody = await emitJson(
        { ok: false, error: error.message },
        args.out,
      );
      if (!args.quiet) {
        process.stdout.write(failureBody);
      }
    }
    process.exit(1);
  }
}

run();
