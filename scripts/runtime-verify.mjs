#!/usr/bin/env node
import { spawnSync } from 'node:child_process';
import { readFile, writeFile, mkdir } from 'node:fs/promises';
import { parseArgs } from 'node:util';
import { dirname, join, resolve, relative, isAbsolute } from 'node:path';
import { fileURLToPath } from 'node:url';

import { canonicalStringify } from './hash-jsonl.mjs';
import { sha256OfCanonicalJson } from '../packages/tf-l0-tools/lib/digest.mjs';

const here = dirname(fileURLToPath(import.meta.url));
const rootDir = resolve(here, '..');
const validateScript = fileURLToPath(new URL('./validate-trace.mjs', import.meta.url));
const verifyScript = fileURLToPath(new URL('../packages/tf-compose/bin/tf-verify-trace.mjs', import.meta.url));
const defaultCatalogPath = join(rootDir, 'packages', 'tf-l0-spec', 'spec', 'catalog.json');

function resolvePilotOutDir() {
  const override = process.env.PILOT_OUT_DIR;
  if (override && override.trim()) {
    return isAbsolute(override) ? override : resolve(rootDir, override);
  }
  return join(rootDir, 'out', '0.4', 'pilot-l0');
}

function resolveFlowPaths(flow) {
  if (flow !== 'pilot') return null;
  const base = resolvePilotOutDir();
  return {
    ir: join(base, 'pilot_min.ir.json'),
    manifest: join(base, 'pilot_min.manifest.json'),
    status: join(base, 'status.json'),
    trace: join(base, 'trace.jsonl'),
    catalog: defaultCatalogPath,
  };
}

function resolveInputPath(value) {
  if (!value) return null;
  if (isAbsolute(value)) return value;
  return resolve(process.cwd(), value);
}

function displayPath(absPath) {
  if (!absPath) return null;
  const rel = relative(rootDir, absPath);
  if (!rel.startsWith('..')) return rel.split('\\').join('/');
  return absPath.split('\\').join('/');
}

async function readJson(path) {
  const raw = await readFile(path, 'utf8');
  try {
    return JSON.parse(raw);
  } catch (err) {
    throw new Error(`unable to parse JSON from ${path}: ${err?.message || err}`);
  }
}

async function digestFromJsonFile(path) {
  const parsed = await readJson(path);
  return sha256OfCanonicalJson(parsed);
}

function parseJsonSafe(raw) {
  if (!raw) return null;
  try {
    return JSON.parse(raw);
  } catch {
    return null;
  }
}

function evaluateStep(name, result) {
  const stdout = (result.stdout || '').trim();
  const summary = parseJsonSafe(stdout);
  const ok = Boolean(summary?.ok) && result.status === 0;
  const issues = [];
  if (!ok) {
    if (Array.isArray(summary?.issues)) {
      issues.push(...summary.issues);
    }
    const stderr = (result.stderr || '').trim();
    if (stderr) {
      issues.push({ step: name, stderr });
    }
    if (result.error) {
      issues.push({ step: name, error: result.error.message || String(result.error) });
    }
    if (!summary && stdout) {
      issues.push({ step: name, stdout });
    }
  }
  return { ok, summary, issues };
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

  if (!values.out) {
    process.stderr.write('--out is required\n');
    process.exitCode = 2;
    return;
  }

  const outPath = resolveInputPath(values.out);
  const flowPaths = values.flow ? resolveFlowPaths(values.flow) : null;

  if (values.flow && !flowPaths) {
    process.stderr.write(`unsupported flow: ${values.flow}\n`);
    process.exitCode = 2;
    return;
  }

  const irPath = flowPaths?.ir || resolveInputPath(values.ir);
  const manifestPath = flowPaths?.manifest || resolveInputPath(values.manifest);
  const statusPath = flowPaths?.status || resolveInputPath(values.status);
  const tracePath = flowPaths?.trace || resolveInputPath(values.trace);

  if (!irPath || !manifestPath || !statusPath || !tracePath) {
    process.stderr.write('missing required inputs (ir, manifest, status, trace)\n');
    process.exitCode = 2;
    return;
  }

  let catalogPath = flowPaths?.catalog || null;
  let catalogDigest = null;
  if (values.catalog) {
    if (values.catalog.startsWith('sha256:')) {
      catalogDigest = values.catalog;
      catalogPath = null;
    } else {
      catalogPath = resolveInputPath(values.catalog);
    }
  }

  const irHash = await digestFromJsonFile(irPath);
  const manifestHash = await digestFromJsonFile(manifestPath);
  if (catalogPath) {
    catalogDigest = await digestFromJsonFile(catalogPath);
  }

  const statusRaw = await readFile(statusPath, 'utf8');
  const status = parseJsonSafe(statusRaw);
  const provenance = status && typeof status === 'object' ? status.provenance : null;

  if (!catalogDigest && provenance && typeof provenance.catalog_hash === 'string') {
    catalogDigest = provenance.catalog_hash;
  }

  if (!catalogDigest) {
    process.stderr.write('unable to determine catalog digest\n');
    process.exitCode = 2;
    return;
  }

  const traceContent = await readFile(tracePath, 'utf8');
  const validateArgs = [
    '--require-meta',
    '--ir',
    irHash,
    '--manifest',
    manifestHash,
    '--catalog',
    catalogDigest,
  ];

  const validateResult = spawnSync(process.execPath, [validateScript, ...validateArgs], {
    input: traceContent,
    encoding: 'utf8',
  });
  const validateStep = evaluateStep('validate', validateResult);

  const verifyArgs = ['--ir', irPath, '--manifest', manifestPath, '--status', statusPath, '--trace', tracePath];
  if (catalogPath) {
    verifyArgs.push('--catalog', catalogPath);
  }
  if (typeof provenance?.ir_hash === 'string') {
    verifyArgs.push('--ir-hash', provenance.ir_hash);
  }
  if (typeof provenance?.manifest_hash === 'string') {
    verifyArgs.push('--manifest-hash', provenance.manifest_hash);
  }
  if (typeof provenance?.catalog_hash === 'string') {
    verifyArgs.push('--catalog-hash', provenance.catalog_hash);
  }

  const verifyResult = spawnSync(process.execPath, [verifyScript, ...verifyArgs], {
    encoding: 'utf8',
  });
  const verifyStep = evaluateStep('verify', verifyResult);

  const steps = { validate: validateStep.ok, verify: verifyStep.ok };
  const issues = [];
  if (!validateStep.ok) {
    issues.push(...validateStep.issues);
  }
  if (!verifyStep.ok) {
    issues.push(...verifyStep.issues);
  }

  const report = {
    ok: validateStep.ok && verifyStep.ok,
    steps,
    paths: {
      ir: displayPath(irPath),
      manifest: displayPath(manifestPath),
      status: displayPath(statusPath),
      trace: displayPath(tracePath),
    },
    hashes: {
      ir: irHash,
      manifest: manifestHash,
      catalog: catalogDigest,
    },
  };

  if (issues.length > 0) {
    report.issues = issues;
  }

  await mkdir(dirname(outPath), { recursive: true });
  const canonical = canonicalStringify(report) + '\n';
  await writeFile(outPath, canonical);

  if (!report.ok) {
    process.exitCode = 1;
  }
}

if (process.argv[1] === fileURLToPath(import.meta.url)) {
  main(process.argv).catch((err) => {
    process.stderr.write(`${err?.message || err}\n`);
    process.exitCode = 1;
  });
}
