#!/usr/bin/env node
import { readdir, readFile, writeFile, mkdir } from 'node:fs/promises';
import { resolve, join, dirname } from 'node:path';

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

function parseCommutePair(law) {
  if (!law.startsWith('commute:')) return null;
  const raw = law.slice('commute:'.length);
  const [left, right] = raw.split('-with-');
  if (!left || !right) return null;
  return [left, right];
}

function collectMissingPairs(missing) {
  const entries = new Set();
  missing.forEach((law) => {
    const pair = parseCommutePair(law);
    if (!pair) return;
    entries.add(JSON.stringify(pair));
  });
  const pairs = Array.from(entries, (entry) => JSON.parse(entry));
  pairs.sort((a, b) => a[0].localeCompare(b[0]) || a[1].localeCompare(b[1]));
  return pairs;
}

async function writeCoverageReport({ outRoot, versions, report }) {
  const serialized = `${JSON.stringify(report, null, 2)}\n`;
  const uniquePaths = new Set();
  for (const version of versions) {
    const candidate = resolve(process.cwd(), outRoot, version, 'proofs', 'coverage.json');
    uniquePaths.add(candidate);
  }
  for (const outputPath of uniquePaths) {
    await mkdir(dirname(outputPath), { recursive: true });
    await writeFile(outputPath, serialized, 'utf8');
  }
}

async function main() {
  const { outRoot } = parseArgs();
  const candidateVersions = ['0.4', '0.5'];
  let manifestVersion = candidateVersions[0];
  let manifestPaths = [];
  for (const version of candidateVersions) {
    const proofsRoot = resolve(process.cwd(), outRoot, version, 'proofs');
    const entries = await collectManifestPaths(proofsRoot);
    if (entries.length > 0) {
      manifestVersion = version;
      manifestPaths = entries;
      break;
    }
  }
  const stubCatalog = await loadStubCatalog();
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
  const report = {
    generated_at: '1970-01-01T00:00:00.000Z',
    ok: payload.ok,
    manifest_version: manifestVersion,
    used_laws: sortedUsed,
    covered_laws: covered,
    missing_laws: missing,
    missing_laws_for_used: collectMissingPairs(missing),
  };
  await writeCoverageReport({
    outRoot,
    versions: new Set([manifestVersion, '0.4']),
    report,
  });
  process.stdout.write(`${JSON.stringify(payload, null, 2)}\n`);
  process.exit(payload.ok ? 0 : 1);
}

main().catch((error) => {
  console.error(error);
  process.exit(1);
});
