#!/usr/bin/env node
import { readdir, readFile } from 'node:fs/promises';
import { resolve, join } from 'node:path';

import { canonicalLawName } from '../../packages/tf-opt/lib/data.mjs';

function parseArgs() {
  const args = process.argv.slice(2);
  const options = {
    outRoot: 'out',
  };
  for (let i = 0; i < args.length; i += 1) {
    const flag = args[i];
    if (flag === '--out' && i + 1 < args.length) {
      options.outRoot = args[i + 1];
      i += 1;
    }
  }
  return options;
}

async function listEntries(dir) {
  try {
    return await readdir(dir, { withFileTypes: true });
  } catch (error) {
    if (error && error.code === 'ENOENT') {
      return [];
    }
    throw error;
  }
}

function lawFromStubName(filename) {
  if (!filename.endsWith('.smt2')) {
    return null;
  }
  const base = filename.slice(0, -'.smt2'.length);
  const restored = base.replace(/__/g, ':');
  const law = canonicalLawName(restored);
  return law.length > 0 ? law : null;
}

async function loadStubCatalog() {
  const dir = resolve(process.cwd(), 'scripts/proofs/laws');
  const entries = await listEntries(dir);
  const names = [];
  for (const entry of entries) {
    if (!entry.isFile()) {
      continue;
    }
    const law = lawFromStubName(entry.name);
    if (law) {
      names.push(law);
    }
  }
  names.sort((a, b) => a.localeCompare(b));
  return new Set(names);
}

async function collectManifestPaths(rootDir) {
  const stack = [rootDir];
  const files = [];
  while (stack.length > 0) {
    const current = stack.pop();
    const entries = await listEntries(current);
    for (const entry of entries) {
      const fullPath = join(current, entry.name);
      if (entry.isDirectory()) {
        stack.push(fullPath);
      } else if (entry.isFile() && entry.name.endsWith('.json')) {
        files.push(fullPath);
      }
    }
  }
  files.sort((a, b) => a.localeCompare(b));
  return files;
}

function extractLaws(manifest) {
  const collected = [];
  const used = manifest && Array.isArray(manifest.used_laws) ? manifest.used_laws : [];
  for (const entry of used) {
    if (typeof entry === 'string') {
      const law = canonicalLawName(entry);
      if (law) {
        collected.push(law);
      }
      continue;
    }
    if (entry && typeof entry === 'object' && typeof entry.law === 'string') {
      const law = canonicalLawName(entry.law);
      if (law) {
        collected.push(law);
      }
    }
  }
  return collected;
}

async function loadUsedLaws(manifestPaths) {
  const laws = new Set();
  for (const manifestPath of manifestPaths) {
    try {
      const raw = await readFile(manifestPath, 'utf8');
      const manifest = JSON.parse(raw);
      const entries = extractLaws(manifest);
      for (const law of entries) {
        laws.add(law);
      }
    } catch (error) {
      error.message = `Failed to load ${manifestPath}: ${error.message}`;
      throw error;
    }
  }
  return laws;
}

async function main() {
  const { outRoot } = parseArgs();
  const proofsRoot = resolve(process.cwd(), outRoot, '0.5', 'proofs');
  const [stubCatalog, manifestPaths] = await Promise.all([
    loadStubCatalog(),
    collectManifestPaths(proofsRoot),
  ]);
  const usedLaws = await loadUsedLaws(manifestPaths);
  const missing = [];
  const covered = [];
  const sortedUsed = Array.from(usedLaws).sort((a, b) => a.localeCompare(b));
  for (const law of sortedUsed) {
    if (stubCatalog.has(law)) {
      covered.push(law);
    } else {
      missing.push(law);
    }
  }
  const payload = {
    ok: missing.length === 0,
    missing,
    covered,
  };
  process.stdout.write(`${JSON.stringify(payload, null, 2)}\n`);
  process.exit(payload.ok ? 0 : 1);
}

main().catch((error) => {
  console.error(error);
  process.exit(1);
});
