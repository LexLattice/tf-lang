#!/usr/bin/env node
import { spawnSync } from 'node:child_process';
import { readFile, writeFile, mkdir } from 'node:fs/promises';
import { dirname, join, resolve, relative } from 'node:path';
import { fileURLToPath } from 'node:url';
import { parseArgs } from 'node:util';

import { hashJsonLike } from './hash-jsonl.mjs';
import { sha256OfCanonicalJson } from '../packages/tf-l0-tools/lib/digest.mjs';

const here = dirname(fileURLToPath(import.meta.url));
const rootDir = resolve(here, '..');

function toRelative(path) {
  if (!path) return null;
  const rel = relative(rootDir, path);
  return rel && !rel.startsWith('..') ? rel : path;
}

async function loadStatus(path) {
  const raw = await readFile(path, 'utf8');
  return JSON.parse(raw);
}

function spawnJson(commandArgs, options = {}) {
  const { input } = options;
  const proc = spawnSync(process.execPath, commandArgs, {
    encoding: 'utf8',
    cwd: rootDir,
    input,
    maxBuffer: 10 * 1024 * 1024,
  });
  const stdout = proc.stdout || '';
  const stderr = proc.stderr || '';
  let parsed = null;
  const text = stdout.trim();
  if (text) {
    try {
      parsed = JSON.parse(text);
    } catch (err) {
      if (!commandArgs.includes('--help')) {
        parsed = null;
      }
    }
  }
  return { status: proc.status, error: proc.error, stdout, stderr, parsed };
}

async function main(argv) {
  const { values, positionals } = parseArgs({
    args: argv.slice(2),
    options: {
      flow: { type: 'string' },
      ir: { type: 'string' },
      manifest: { type: 'string' },
      status: { type: 'string' },
      trace: { type: 'string' },
      out: { type: 'string' },
      catalog: { type: 'string' },
    },
    allowPositionals: true,
  });

  if (positionals.length > 0) {
    console.error(`unexpected positional argument: ${positionals[0]}`);
    process.exitCode = 1;
    return;
  }

  const outPath = values.out ? resolve(rootDir, values.out) : null;
  if (!outPath) {
    console.error('missing required --out path');
    process.exitCode = 1;
    return;
  }

  let irPath = values.ir ? resolve(rootDir, values.ir) : null;
  let manifestPath = values.manifest ? resolve(rootDir, values.manifest) : null;
  let statusPath = values.status ? resolve(rootDir, values.status) : null;
  let tracePath = values.trace ? resolve(rootDir, values.trace) : null;
  let catalogPath = values.catalog ? resolve(rootDir, values.catalog) : null;

  if (values.flow) {
    if (values.flow !== 'pilot') {
      console.error(`unsupported flow: ${values.flow}`);
      process.exitCode = 1;
      return;
    }
    const flowDir = join(rootDir, 'out', '0.4', 'pilot-l0');
    irPath = join(flowDir, 'pilot_min.ir.json');
    manifestPath = join(flowDir, 'pilot_min.manifest.json');
    statusPath = join(flowDir, 'status.json');
    tracePath = join(flowDir, 'trace.jsonl');
  }

  if (!irPath || !manifestPath || !statusPath || !tracePath) {
    console.error('missing required artifact paths');
    process.exitCode = 1;
    return;
  }

  const traceContent = await readFile(tracePath, 'utf8');
  const status = await loadStatus(statusPath);
  const provenance = status && typeof status.provenance === 'object' && !Array.isArray(status.provenance)
    ? status.provenance
    : null;

  const irSource = await readFile(irPath, 'utf8');
  const irHash = sha256OfCanonicalJson(JSON.parse(irSource));
  const manifestHash = await hashJsonLike(manifestPath);

  let catalogHash = null;
  if (catalogPath) {
    catalogHash = await hashJsonLike(catalogPath);
  }
  if (!catalogHash && provenance && typeof provenance.catalog_hash === 'string') {
    catalogHash = provenance.catalog_hash;
  }

  const validateArgs = [
    join('scripts', 'validate-trace.mjs'),
    '--require-meta',
    '--ir',
    irHash,
    '--manifest',
    manifestHash,
  ];
  if (catalogHash) {
    validateArgs.push('--catalog', catalogHash);
  }

  const validateResult = spawnJson(validateArgs, { input: traceContent });
  const validateOk = validateResult.status === 0;
  const validateIssues = validateResult.parsed?.issues;

  const verifyArgs = [
    join('packages', 'tf-compose', 'bin', 'tf-verify-trace.mjs'),
    '--ir',
    irPath,
    '--manifest',
    manifestPath,
    '--status',
    statusPath,
    '--trace',
    tracePath,
    '--ir-hash',
    irHash,
    '--manifest-hash',
    manifestHash,
  ];
  if (catalogPath) {
    verifyArgs.push('--catalog', catalogPath);
  }
  if (catalogHash) {
    verifyArgs.push('--catalog-hash', catalogHash);
  }

  const verifyResult = spawnJson(verifyArgs);
  const verifyOk = verifyResult.status === 0;
  const verifyIssues = verifyResult.parsed?.issues;

  const ok = validateOk && verifyOk;
  const report = {
    ok,
    steps: {
      validate: validateOk,
      verify: verifyOk,
    },
    paths: {
      ir: toRelative(irPath),
      manifest: toRelative(manifestPath),
      status: toRelative(statusPath),
      trace: toRelative(tracePath),
    },
    hashes: {
      ir: irHash,
      manifest: manifestHash,
      catalog: catalogHash || null,
    },
  };

  const issues = [];
  if (!validateOk) {
    if (Array.isArray(validateIssues) && validateIssues.length > 0) {
      issues.push(...validateIssues);
    } else {
      issues.push({ step: 'validate', stderr: validateResult.stderr?.trim() || 'validate failed' });
    }
  }
  if (!verifyOk) {
    if (Array.isArray(verifyIssues) && verifyIssues.length > 0) {
      issues.push(...verifyIssues);
    } else {
      issues.push({ step: 'verify', stderr: verifyResult.stderr?.trim() || 'verify failed' });
    }
  }
  if (issues.length > 0) {
    report.issues = issues;
  }

  await mkdir(dirname(outPath), { recursive: true });
  const payload = JSON.stringify(report) + '\n';
  await writeFile(outPath, payload);

  if (!ok) {
    process.exitCode = 1;
  }
}

main(process.argv).catch((err) => {
  console.error(err?.stack || err?.message || String(err));
  process.exitCode = 1;
});
