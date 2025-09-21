#!/usr/bin/env node
import { promises as fs } from 'node:fs';
import { mkdir } from 'node:fs/promises';
import { dirname, join, resolve, relative, isAbsolute } from 'node:path';
import { fileURLToPath } from 'node:url';
import { parseArgs } from 'node:util';
import { spawn } from 'node:child_process';

import { sha256OfCanonicalJson } from '../packages/tf-l0-tools/lib/digest.mjs';

const here = dirname(fileURLToPath(import.meta.url));
const rootDir = resolve(here, '..');
const validateTraceScript = join(rootDir, 'scripts', 'validate-trace.mjs');
const verifyTraceScript = join(rootDir, 'packages', 'tf-compose', 'bin', 'tf-verify-trace.mjs');
function resolvePilotOutDir() {
  const override = process.env.PILOT_OUT_DIR;
  if (override && override.trim()) {
    return isAbsolute(override) ? override : join(rootDir, override);
  }
  return join(rootDir, 'out', '0.4', 'pilot-l0');
}

const pilotOutDir = resolvePilotOutDir();
const pilotCatalogPath = join(rootDir, 'packages', 'tf-l0-spec', 'spec', 'catalog.json');

function normalizePath(pathValue) {
  const rel = relative(rootDir, pathValue);
  if (!rel || rel.startsWith('..')) {
    return pathValue;
  }
  return rel.split(/\\+/).join('/');
}

async function readJson(pathValue) {
  const raw = await fs.readFile(pathValue, 'utf8');
  return JSON.parse(raw);
}

async function hashJson(pathValue) {
  const raw = await fs.readFile(pathValue, 'utf8');
  const parsed = JSON.parse(raw);
  return sha256OfCanonicalJson(parsed);
}

function parseHashOption(value) {
  if (!value) return { hash: null, path: null };
  if (value.startsWith('sha256:')) {
    return { hash: value, path: null };
  }
  return { hash: null, path: resolve(value) };
}

function runNode(scriptPath, args, { input } = {}) {
  return new Promise((resolvePromise, rejectPromise) => {
    const child = spawn(process.execPath, [scriptPath, ...args], {
      stdio: ['pipe', 'pipe', 'pipe'],
    });

    let stdout = '';
    let stderr = '';

    child.stdout.setEncoding('utf8');
    child.stderr.setEncoding('utf8');

    child.stdout.on('data', (chunk) => {
      stdout += chunk;
    });

    child.stderr.on('data', (chunk) => {
      stderr += chunk;
    });

    child.on('error', (err) => {
      rejectPromise(err);
    });

    child.on('close', (code) => {
      resolvePromise({ code, stdout, stderr });
    });

    if (typeof input === 'string') {
      child.stdin.write(input);
    }
    child.stdin.end();
  });
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
      catalog: { type: 'string' },
      out: { type: 'string' },
    },
    allowPositionals: true,
  });

  if (positionals.length > 0) {
    process.stderr.write(`unexpected positional argument: ${positionals[0]}\n`);
    process.exitCode = 2;
    return;
  }

  const outFlag = values.out;
  if (!outFlag || typeof outFlag !== 'string') {
    process.stderr.write('--out <file> is required\n');
    process.exitCode = 2;
    return;
  }

  const flow = values.flow;
  let resolved = null;
  const catalogOption = parseHashOption(typeof values.catalog === 'string' ? values.catalog : '');

  if (flow) {
    if (flow !== 'pilot') {
      process.stderr.write(`unsupported flow: ${flow}\n`);
      process.exitCode = 2;
      return;
    }
    resolved = {
      ir: join(pilotOutDir, 'pilot_min.ir.json'),
      manifest: join(pilotOutDir, 'pilot_min.manifest.json'),
      status: join(pilotOutDir, 'status.json'),
      trace: join(pilotOutDir, 'trace.jsonl'),
      catalogPath: catalogOption.path || pilotCatalogPath,
    };
  } else {
    const ir = values.ir;
    const manifest = values.manifest;
    const status = values.status;
    const trace = values.trace;
    if (!ir || !manifest || !status || !trace) {
      process.stderr.write('--ir, --manifest, --status, and --trace are required without --flow\n');
      process.exitCode = 2;
      return;
    }
    resolved = {
      ir: resolve(ir),
      manifest: resolve(manifest),
      status: resolve(status),
      trace: resolve(trace),
      catalogPath: catalogOption.path,
    };
  }

  const outPath = resolve(outFlag);

  const paths = {
    ir: resolved.ir,
    manifest: resolved.manifest,
    status: resolved.status,
    trace: resolved.trace,
  };

  const status = await readJson(paths.status);
  const provenance = status && typeof status.provenance === 'object' && !Array.isArray(status.provenance)
    ? status.provenance
    : {};

  const irHash = await hashJson(paths.ir);
  const manifestHash = await hashJson(paths.manifest);

  let catalogHash = catalogOption.hash || null;
  let catalogSourcePath = resolved.catalogPath || null;

  if (!catalogHash && catalogSourcePath) {
    catalogHash = await hashJson(catalogSourcePath);
  }

  if (!catalogHash && typeof provenance.catalog_hash === 'string') {
    catalogHash = provenance.catalog_hash;
  }

  if (!catalogHash) {
    process.stderr.write('unable to determine catalog hash (provide --catalog or provenance)\n');
    process.exitCode = 2;
    return;
  }

  if (typeof provenance.catalog_hash === 'string' && catalogHash !== provenance.catalog_hash) {
    process.stderr.write('warning: catalog hash mismatch between status and provided value\n');
  }

  const traceInput = await fs.readFile(paths.trace, 'utf8');

  const report = {
    ok: false,
    steps: { validate: false, verify: false },
    paths: Object.fromEntries(
      Object.entries(paths).map(([key, value]) => [key, normalizePath(value)]),
    ),
    hashes: {
      ir: irHash,
      manifest: manifestHash,
      catalog: catalogHash,
    },
  };

  const validateArgs = [
    '--require-meta',
    '--ir',
    irHash,
    '--manifest',
    manifestHash,
    '--catalog',
    catalogHash,
  ];

  const validateResult = await runNode(validateTraceScript, validateArgs, { input: traceInput });

  let validateSummary = null;
  if (validateResult.stdout.trim()) {
    try {
      validateSummary = JSON.parse(validateResult.stdout.trim());
    } catch (err) {
      process.stderr.write(`unable to parse validate output: ${err?.message || err}\n`);
    }
  }

  if (validateResult.code === 0 && validateSummary && validateSummary.ok) {
    report.steps.validate = true;
  } else {
    report.ok = false;
    if (validateSummary && Array.isArray(validateSummary.issues)) {
      report.issues = validateSummary.issues;
    } else if (validateResult.stderr) {
      report.issues = [validateResult.stderr.trim()];
    } else {
      report.issues = ['validate_failed'];
    }
    await mkdir(dirname(outPath), { recursive: true });
    await fs.writeFile(outPath, JSON.stringify(report) + '\n');
    process.exitCode = 1;
    return;
  }

  const verifyArgs = [
    '--ir',
    paths.ir,
    '--manifest',
    paths.manifest,
    '--status',
    paths.status,
    '--trace',
    paths.trace,
  ];

  const verifyResult = await runNode(verifyTraceScript, verifyArgs);

  let verifySummary = null;
  if (verifyResult.stdout.trim()) {
    try {
      verifySummary = JSON.parse(verifyResult.stdout.trim());
    } catch (err) {
      process.stderr.write(`unable to parse verify output: ${err?.message || err}\n`);
    }
  }

  if (verifyResult.code === 0 && verifySummary && verifySummary.ok) {
    report.steps.verify = true;
    report.ok = true;
  } else {
    report.ok = false;
    if (verifySummary && Array.isArray(verifySummary.issues)) {
      report.issues = verifySummary.issues;
    } else if (verifyResult.stderr) {
      report.issues = [verifyResult.stderr.trim()];
    } else {
      report.issues = ['verify_failed'];
    }
  }

  await mkdir(dirname(outPath), { recursive: true });
  await fs.writeFile(outPath, JSON.stringify(report) + '\n');

  if (!report.ok) {
    process.exitCode = 1;
  }
}

main(process.argv).catch((err) => {
  process.stderr.write(`${err?.stack || err?.message || err}\n`);
  process.exitCode = 1;
});
