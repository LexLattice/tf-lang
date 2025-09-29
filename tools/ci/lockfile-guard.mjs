#!/usr/bin/env node
import { execSync } from 'node:child_process';

const DEFAULT_IGNORE_PREFIXES = ['vendor/', 'third_party/'];

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

function getIgnorePrefixes() {
  const raw = process.env.LOCK_GUARD_IGNORE_PREFIXES;
  if (!raw) {
    return DEFAULT_IGNORE_PREFIXES;
  }
  return raw
    .split(/[,:]/)
    .map((item) => item.trim())
    .filter(Boolean);
}

function shouldIgnore(path, prefixes) {
  return prefixes.some((prefix) => path.startsWith(prefix));
}

function getPorcelainPaths() {
  let raw = '';
  try {
    raw = execSync('git status --porcelain=v1 -z', { encoding: 'utf8' });
  } catch (error) {
    return new Set();
  }

  const paths = new Set();
  if (!raw) {
    return paths;
  }

  const entries = raw.split('\0');
  for (let i = 0; i < entries.length; i += 1) {
    const entry = entries[i];
    if (!entry) {
      continue;
    }

    const status = entry.slice(0, 2);
    const filePath = entry.slice(3).trim();

    if (!filePath) {
      continue;
    }

    if ((status[0] === 'R' || status[0] === 'C') && i + 1 < entries.length) {
      const newPath = entries[i + 1]?.trim();
      paths.add(filePath);
      if (newPath) {
        paths.add(newPath);
      }
      i += 1;
      continue;
    }

    paths.add(filePath);
  }

  return paths;
}

function formatFailureHint(paths) {
  if (!paths.length) {
    return '';
  }
  const maxList = 10;
  const shown = paths.slice(0, maxList);
  const remainder = paths.length - shown.length;
  const lines = [
    'package.json changed without pnpm-lock.yaml update:',
    ...shown.map((item) => `  - ${item}`),
  ];
  if (remainder > 0) {
    lines.push(`  … (+${remainder} more)`);
  }
  return lines.join('\n');
}

function main() {
  const options = parseArgs(process.argv.slice(2));
  const ignorePrefixes = getIgnorePrefixes();
  const paths = getPorcelainPaths();
  const filteredSet = new Set(
    Array.from(paths).filter((p) => !shouldIgnore(p, ignorePrefixes)),
  );
  const filteredPaths = Array.from(filteredSet);
  const changedPackages = filteredPaths
    .filter((p) => p.endsWith('package.json'))
    .sort();
  const lockfileChanged = filteredSet.has('pnpm-lock.yaml');
  const ok = changedPackages.length === 0 || lockfileChanged;

  const payload = {
    ok,
    changed_packages: changedPackages,
    lockfile_changed: lockfileChanged,
    ignored_prefixes: ignorePrefixes,
  };

  if (!ok) {
    const hint = formatFailureHint(changedPackages);
    if (hint) {
      console.error(hint);
    }
  }

  emit(payload, options);
  process.exit(ok ? 0 : 1);
}

main();
