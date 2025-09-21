#!/usr/bin/env node
import { promises as fs } from 'node:fs';
import { mkdir } from 'node:fs/promises';
import { dirname, join, resolve, relative, isAbsolute } from 'node:path';
import { fileURLToPath } from 'node:url';
import { parseArgs } from 'node:util';
import { spawn } from 'node:child_process';

import { canonicalJson } from '../packages/utils/dist/index.js';
import { sha256OfCanonicalJson, sha256OfJsonl } from '../packages/tf-l0-tools/lib/digest.mjs';

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

function resolveSigningOutDir() {
  const override = process.env.SIGNING_OUT_DIR;
  if (override && override.trim()) {
    return isAbsolute(override) ? override : join(rootDir, override);
  }
  return join(rootDir, 'out', '0.4', 'signing-l0');
}

const flowResolvers = {
  pilot: () => {
    const dir = resolvePilotOutDir();
    return {
      ir: join(dir, 'pilot_min.ir.json'),
      manifest: join(dir, 'pilot_min.manifest.json'),
      status: join(dir, 'status.json'),
      trace: join(dir, 'trace.jsonl'),
      catalog: join(dir, 'catalog.json'),
    };
  },
  signing: () => {
    const dir = resolveSigningOutDir();
    return {
      ir: join(dir, 'signing.ir.json'),
      manifest: join(dir, 'signing.manifest.json'),
      status: join(dir, 'status.json'),
      trace: join(dir, 'trace.jsonl'),
      catalog: join(dir, 'catalog.json'),
    };
  },
};

function normalizePath(pathValue) {
  const rel = relative(rootDir, pathValue);
  if (!rel || rel.startsWith('..')) {
    return pathValue;
  }
  return rel.split(/\\+/).join('/');
}

function isShaLiteral(value) {
  return typeof value === 'string' && /^sha256:[0-9a-f]{64}$/i.test(value.trim());
}

function printHelp() {
  const lines = [
    'Usage: node scripts/runtime-verify.mjs [--flow <pilot|signing>] [--options]',
    '',
    'Options:',
    '  --out <file>             Path to write the verification report (required).',
    '  --flow <name>            Known flows: pilot (default), signing.',
    '  --ir <file>              Override IR artifact path.',
    '  --manifest <file>        Override manifest path.',
    '  --status <file>          Override status path.',
    '  --trace <file>           Override trace path.',
    '  --catalog <file>         Override catalog path.',
    '  --catalog-hash <sha>     Expected catalog hash (defaults to provenance).',
    '  --print-inputs           Echo resolved inputs before verification.',
    '  --help                   Show this help message.',
    '',
    'Without explicit paths the CLI resolves flow artifacts from the repository.',
    'Manual mode requires --ir, --manifest, --status, --trace, and --catalog.',
  ];
  process.stdout.write(`${lines.join('\n')}\n`);
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

async function hashJsonFile(pathValue) {
  const raw = await fs.readFile(pathValue, 'utf8');
  const parsed = JSON.parse(raw);
  return sha256OfCanonicalJson(parsed);
}

async function ensureFile(pathValue, label) {
  try {
    await fs.access(pathValue);
  } catch (err) {
    process.stderr.write(`missing ${label}: ${pathValue}\n`);
    process.exitCode = 2;
    throw err;
  }
}

async function writeReport(outPath, report) {
  await mkdir(dirname(outPath), { recursive: true });
  await fs.writeFile(outPath, canonicalJson(report));
}

async function main(argv) {
  const { values, positionals } = parseArgs({
    args: argv.slice(2),
    options: {
      help: { type: 'boolean' },
      flow: { type: 'string' },
      ir: { type: 'string' },
      manifest: { type: 'string' },
      status: { type: 'string' },
      trace: { type: 'string' },
      catalog: { type: 'string' },
      'catalog-hash': { type: 'string' },
      out: { type: 'string' },
      'print-inputs': { type: 'boolean' },
    },
    allowPositionals: true,
  });

  if (values.help) {
    printHelp();
    return;
  }

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
  const outPath = resolve(outFlag);

  const explicitPathsProvided = ['ir', 'manifest', 'status', 'trace', 'catalog'].some(
    (key) => typeof values[key] === 'string',
  );

  let flow = values.flow;
  if (!flow && !explicitPathsProvided) {
    flow = 'pilot';
  }
  if (flow) {
    flow = flow.toLowerCase();
    if (!Object.prototype.hasOwnProperty.call(flowResolvers, flow)) {
      process.stderr.write(`unsupported flow: ${flow}\n`);
      process.exitCode = 2;
      return;
    }
  }

  let resolvedPaths = null;
  if (flow) {
    resolvedPaths = flowResolvers[flow]();
  } else {
    const requiredFlags = ['ir', 'manifest', 'status', 'trace', 'catalog'];
    for (const flag of requiredFlags) {
      if (!values[flag]) {
        process.stderr.write('manual mode requires --ir, --manifest, --status, --trace, and --catalog\n');
        process.exitCode = 2;
        return;
      }
    }
    resolvedPaths = {
      ir: resolve(values.ir),
      manifest: resolve(values.manifest),
      status: resolve(values.status),
      trace: resolve(values.trace),
      catalog: resolve(values.catalog),
    };
  }

  const overrides = {};
  for (const key of ['ir', 'manifest', 'status', 'trace', 'catalog']) {
    const value = values[key];
    if (typeof value === 'string') {
      if (key === 'catalog' && isShaLiteral(value)) {
        process.stderr.write('--catalog requires a file path when verification is enabled\n');
        process.exitCode = 2;
        return;
      }
      overrides[key] = resolve(value);
    }
  }
  resolvedPaths = { ...resolvedPaths, ...overrides };

  for (const [label, pathValue] of Object.entries(resolvedPaths)) {
    try {
      await ensureFile(pathValue, label);
    } catch (err) {
      return;
    }
  }

  const statusRaw = await fs.readFile(resolvedPaths.status, 'utf8');
  const statusJson = JSON.parse(statusRaw);
  const provenance =
    statusJson && typeof statusJson.provenance === 'object' && !Array.isArray(statusJson.provenance)
      ? statusJson.provenance
      : {};

  const irHash = await hashJsonFile(resolvedPaths.ir);
  const manifestHash = await hashJsonFile(resolvedPaths.manifest);
  const statusHash = await hashJsonFile(resolvedPaths.status);
  const traceHash = await sha256OfJsonl(resolvedPaths.trace);
  const catalogHash = await hashJsonFile(resolvedPaths.catalog);

  let expectedCatalogHash = null;
  if (typeof values['catalog-hash'] === 'string' && values['catalog-hash'].trim()) {
    const trimmed = values['catalog-hash'].trim();
    if (!isShaLiteral(trimmed)) {
      process.stderr.write('--catalog-hash must be a sha256:<hex> literal\n');
      process.exitCode = 2;
      return;
    }
    expectedCatalogHash = trimmed;
  }
  if (!expectedCatalogHash && typeof provenance.catalog_hash === 'string') {
    expectedCatalogHash = provenance.catalog_hash;
  }
  if (!expectedCatalogHash) {
    expectedCatalogHash = catalogHash;
  }

  const normalizedPaths = Object.fromEntries(
    Object.entries(resolvedPaths).map(([key, value]) => [key, normalizePath(value)]),
  );

  const inputs = {
    ir: { path: normalizedPaths.ir, sha256: irHash },
    manifest: { path: normalizedPaths.manifest, sha256: manifestHash },
    status: { path: normalizedPaths.status, sha256: statusHash },
    trace: { path: normalizedPaths.trace, sha256: traceHash },
    catalog: { path: normalizedPaths.catalog, sha256: catalogHash },
  };
  if (expectedCatalogHash) {
    inputs.catalog.expected = expectedCatalogHash;
  }

  if (values['print-inputs']) {
    for (const [key, info] of Object.entries(inputs)) {
      const lineParts = [`${key}: ${info.path}`];
      if (info.sha256) {
        lineParts.push(`sha=${info.sha256}`);
      }
      if (key === 'catalog' && expectedCatalogHash) {
        lineParts.push(`expected=${expectedCatalogHash}`);
      }
      process.stdout.write(`${lineParts.join(' ')}\n`);
    }
  }

  const report = {
    ok: false,
    flow: flow || 'manual',
    steps: { validate: false, verify: false },
    inputs,
    paths: normalizedPaths,
  };

  const validateArgs = ['--require-meta', '--ir', irHash, '--manifest', manifestHash];
  if (expectedCatalogHash) {
    validateArgs.push('--catalog', expectedCatalogHash);
  }

  const traceInput = await fs.readFile(resolvedPaths.trace, 'utf8');
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
    await writeReport(outPath, report);
    process.exitCode = 3;
    return;
  }

  const verifyArgs = [
    '--ir',
    resolvedPaths.ir,
    '--manifest',
    resolvedPaths.manifest,
    '--status',
    resolvedPaths.status,
    '--trace',
    resolvedPaths.trace,
    '--catalog',
    resolvedPaths.catalog,
    '--catalog-hash',
    expectedCatalogHash,
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
    await writeReport(outPath, report);
    process.exitCode = 3;
    return;
  }

  await writeReport(outPath, report);
}

main(process.argv).catch((err) => {
  process.stderr.write(`${err?.stack || err?.message || err}\n`);
  if (!process.exitCode) {
    process.exitCode = 1;
  }
});
