#!/usr/bin/env node
// scripts/runtime-verify.mjs
import { spawnSync } from 'node:child_process';
import { readFile, writeFile, mkdir } from 'node:fs/promises';
import { dirname, join, resolve, relative, isAbsolute } from 'node:path';
import { fileURLToPath } from 'node:url';
import { parseArgs } from 'node:util';

import { canonicalStringify } from './hash-jsonl.mjs';

function isShaLiteral(value) {
  return typeof value === 'string' && /^sha256:[0-9a-f]{64}$/i.test(value);
}

function formatPath(rootDir, filePath) {
  if (!filePath) return '';
  const rel = relative(rootDir, filePath);
  if (!rel || rel.startsWith('..')) return filePath;
  return rel === '' ? '.' : rel;
}

function resolveMaybeRelative(rootDir, value) {
  if (!value) return value;
  if (isAbsolute(value)) return value;
  return resolve(rootDir, value);
}

function resolvePilotDir(rootDir) {
  const override = process.env.PILOT_OUT_DIR;
  if (override && override.trim()) {
    return isAbsolute(override) ? override : resolve(rootDir, override);
  }
  return join(rootDir, 'out', '0.4', 'pilot-l0');
}

async function readJson(path) {
  const raw = await readFile(path, 'utf8');
  return JSON.parse(raw);
}

function collectStatusHashes(status) {
  const provenance = status && typeof status.provenance === 'object' && !Array.isArray(status.provenance)
    ? status.provenance
    : null;
  if (!provenance) {
    return { issues: ['status: missing provenance'] };
  }
  const ir = typeof provenance.ir_hash === 'string' ? provenance.ir_hash : null;
  const manifest = typeof provenance.manifest_hash === 'string' ? provenance.manifest_hash : null;
  const catalog = typeof provenance.catalog_hash === 'string' ? provenance.catalog_hash : null;
  const issues = [];
  if (!ir) issues.push('status: missing ir_hash');
  if (!manifest) issues.push('status: missing manifest_hash');
  if (!catalog) issues.push('status: missing catalog_hash');
  if (issues.length > 0) {
    return { issues };
  }
  return { hashes: { ir, manifest, catalog } };
}

async function main(argv) {
  const __dirname = dirname(fileURLToPath(import.meta.url));
  const rootDir = resolve(__dirname, '..');
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
    process.stderr.write(`unexpected positional argument: ${positionals[0]}\n`);
    process.exitCode = 2;
    return;
  }

  const outPath = values.out ? resolveMaybeRelative(rootDir, values.out) : null;
  if (!outPath) {
    process.stderr.write('--out is required\n');
    process.exitCode = 2;
    return;
  }

  const flow = values.flow ? values.flow.trim() : '';
  const resolved = {};
  if (flow) {
    if (flow !== 'pilot') {
      process.stderr.write(`unsupported flow: ${flow}\n`);
      process.exitCode = 2;
      return;
    }
    const pilotDir = resolvePilotDir(rootDir);
    resolved.ir = join(pilotDir, 'pilot_min.ir.json');
    resolved.manifest = join(pilotDir, 'pilot_min.manifest.json');
    resolved.status = join(pilotDir, 'status.json');
    resolved.trace = join(pilotDir, 'trace.jsonl');
  } else {
    resolved.ir = values.ir ? resolveMaybeRelative(rootDir, values.ir) : null;
    resolved.manifest = values.manifest ? resolveMaybeRelative(rootDir, values.manifest) : null;
    resolved.status = values.status ? resolveMaybeRelative(rootDir, values.status) : null;
    resolved.trace = values.trace ? resolveMaybeRelative(rootDir, values.trace) : null;
  }

  for (const [key, pathValue] of Object.entries(resolved)) {
    if (!pathValue) {
      process.stderr.write(`missing required --${key} path\n`);
      process.exitCode = 2;
      return;
    }
  }

  const catalogOverride = values.catalog ? values.catalog.trim() : '';
  let status;
  let statusIssues = [];
  try {
    status = await readJson(resolved.status);
  } catch (err) {
    process.stderr.write(`unable to read status: ${err?.message || err}\n`);
    statusIssues.push('status: unreadable');
  }

  let hashes = null;
  if (status) {
    const result = collectStatusHashes(status);
    if (result.hashes) {
      hashes = result.hashes;
    }
    if (result.issues) {
      statusIssues = statusIssues.concat(result.issues);
    }
  }

  if (!hashes && isShaLiteral(catalogOverride)) {
    hashes = {
      ir: null,
      manifest: null,
      catalog: catalogOverride,
    };
  }

  if (!hashes) {
    process.stderr.write('status missing provenance hashes\n');
    process.exitCode = 1;
  }

  const validateScript = join(rootDir, 'scripts', 'validate-trace.mjs');
  const verifyScript = join(rootDir, 'packages', 'tf-compose', 'bin', 'tf-verify-trace.mjs');

  const steps = { validate: false, verify: false };
  const issues = [...statusIssues];

  let validateSummary = null;
  if (hashes) {
    const traceData = await readFile(resolved.trace, 'utf8');
    const args = [
      validateScript,
      '--require-meta',
    ];
    if (hashes.ir) {
      args.push('--ir', hashes.ir);
    }
    if (hashes.manifest) {
      args.push('--manifest', hashes.manifest);
    }
    const catalogValue = catalogOverride || hashes.catalog;
    if (catalogValue) {
      args.push('--catalog', catalogValue);
    }
    const validateResult = spawnSync(process.execPath, args, {
      input: traceData,
      encoding: 'utf8',
    });
    const stdout = (validateResult.stdout || '').trim();
    if (stdout) {
      try {
        validateSummary = JSON.parse(stdout);
      } catch (err) {
        issues.push(`validate: unable to parse output (${err?.message || err})`);
      }
    }
    if (!validateSummary) {
      validateSummary = { ok: validateResult.status === 0 };
    }
    if (validateResult.status !== 0) {
      steps.validate = false;
    } else {
      steps.validate = Boolean(validateSummary.ok);
    }
    if (validateSummary && validateSummary.issues && Array.isArray(validateSummary.issues)) {
      if (!validateSummary.ok) {
        issues.push(...validateSummary.issues);
      }
    }
  }

  let verifySummary = null;
  const verifyArgs = [
    verifyScript,
    '--ir',
    resolved.ir,
    '--manifest',
    resolved.manifest,
    '--status',
    resolved.status,
    '--trace',
    resolved.trace,
  ];
  if (hashes?.ir) {
    verifyArgs.push('--ir-hash', hashes.ir);
  }
  if (hashes?.manifest) {
    verifyArgs.push('--manifest-hash', hashes.manifest);
  }
  if (hashes?.catalog && !catalogOverride) {
    verifyArgs.push('--catalog-hash', hashes.catalog);
  }
  if (catalogOverride && !isShaLiteral(catalogOverride)) {
    verifyArgs.push('--catalog', catalogOverride);
  }
  const verifyResult = spawnSync(process.execPath, verifyArgs, { encoding: 'utf8' });
  const verifyStdout = (verifyResult.stdout || '').trim();
  if (verifyStdout) {
    try {
      verifySummary = JSON.parse(verifyStdout);
    } catch (err) {
      issues.push(`verify: unable to parse output (${err?.message || err})`);
    }
  }
  if (!verifySummary) {
    verifySummary = { ok: verifyResult.status === 0 };
  }
  steps.verify = Boolean(verifySummary.ok);
  if (!verifySummary.ok && Array.isArray(verifySummary.issues)) {
    issues.push(...verifySummary.issues);
  }

  const finalIssues = issues.filter((issue) => issue != null);
  const ok = steps.validate && steps.verify && finalIssues.length === 0;
  const report = {
    ok,
    steps,
    paths: {
      ir: formatPath(rootDir, resolved.ir),
      manifest: formatPath(rootDir, resolved.manifest),
      status: formatPath(rootDir, resolved.status),
      trace: formatPath(rootDir, resolved.trace),
    },
    hashes: {
      ir: hashes?.ir || null,
      manifest: hashes?.manifest || null,
      catalog: hashes?.catalog || (catalogOverride && isShaLiteral(catalogOverride) ? catalogOverride : null),
    },
  };
  if (!ok && finalIssues.length > 0) {
    report.issues = finalIssues;
  }

  await mkdir(dirname(outPath), { recursive: true });
  await writeFile(outPath, canonicalStringify(report) + '\n');

  if (!ok) {
    process.exitCode = 1;
  }
}

main(process.argv).catch((err) => {
  process.stderr.write(`${err?.stack || err?.message || String(err)}\n`);
  process.exitCode = 1;
});
