#!/usr/bin/env node
import { spawnSync } from 'node:child_process';
import { mkdir, readFile, writeFile, rm } from 'node:fs/promises';
import { dirname, join, isAbsolute } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';

import { canonicalStringify, hashJsonLike } from './hash-jsonl.mjs';
import { sha256OfCanonicalJson } from '../packages/tf-l0-tools/lib/digest.mjs';

const here = dirname(fileURLToPath(import.meta.url));
const rootDir = join(here, '..');
const FIXED_TS = process.env.TF_FIXED_TS || '1750000000000';
const baseEnv = { ...process.env, TF_FIXED_TS: String(FIXED_TS) };

const SEED = Number(process.env.TF_PILOT_SEED ?? '42');
const SLICE = process.env.TF_PILOT_SLICE ?? '0:50:1';
const INPUT_CSV = process.env.TF_PILOT_INPUT ?? join(rootDir, 'tests', 'data', 'ticks-mini.csv');

function resolveOutDir() {
  const override = process.env.PILOT_FULL_OUT_DIR;
  if (override && override.trim()) {
    return isAbsolute(override) ? override : join(rootDir, override);
  }
  return join(rootDir, 'out', '0.4', 'pilot-full');
}

const outDir = resolveOutDir();
const codegenDir = join(outDir, 'codegen-ts', 'pilot_full');
const specCatalogPath = join(rootDir, 'packages', 'tf-l0-spec', 'spec', 'catalog.json');
const tfCompose = join(rootDir, 'packages', 'tf-compose', 'bin', 'tf.mjs');
const tfManifest = join(rootDir, 'packages', 'tf-compose', 'bin', 'tf-manifest.mjs');
const traceSummary = join(rootDir, 'packages', 'tf-l0-tools', 'trace-summary.mjs');
const flowPath = join(rootDir, 'examples', 'flows', 'pilot_full.tf');
const pipelineModule = join(rootDir, 'scripts', 'lib', 'pilot-full-pipeline.mjs');

const STORAGE_URI = 'res://pilot-full/';

function sh(cmd, args, options = {}) {
  const env = options.env ? { ...baseEnv, ...options.env } : baseEnv;
  const result = spawnSync(cmd, args, { stdio: 'inherit', ...options, env });
  if (result.status !== 0) {
    process.exit(result.status ?? 1);
  }
}

function rewriteFootprints(list) {
  if (!Array.isArray(list)) return [];
  return list.map((entry) => {
    if (!entry || typeof entry !== 'object') return entry;
    if (typeof entry.uri === 'string' && entry.uri.startsWith('res://kv/')) {
      const updated = { ...entry, uri: STORAGE_URI };
      if (updated.notes === 'seed') updated.notes = 'pilot full write';
      return updated;
    }
    return entry;
  });
}

async function rewriteManifest(path) {
  const manifestRaw = await readFile(path, 'utf8');
  const manifest = JSON.parse(manifestRaw);
  manifest.footprints = rewriteFootprints(manifest.footprints);
  if (manifest.footprints_rw && Array.isArray(manifest.footprints_rw.writes)) {
    manifest.footprints_rw = {
      ...manifest.footprints_rw,
      writes: rewriteFootprints(manifest.footprints_rw.writes),
    };
  }
  await writeFile(path, JSON.stringify(manifest, null, 2) + '\n');
  return manifest;
}

async function patchRunFile(runPath, manifest, manifestHash, irHash) {
  let source = await readFile(runPath, 'utf8');
  if (manifest) {
    const manifestPattern = /const MANIFEST = [^;]*?;\n/;
    source = source.replace(manifestPattern, `const MANIFEST = ${JSON.stringify(manifest)};\n`);
  }
  if (typeof manifestHash === 'string') {
    const manifestHashPattern = /const MANIFEST_HASH = '[^']*';/;
    source = source.replace(manifestHashPattern, `const MANIFEST_HASH = '${manifestHash}';`);
  }
  if (typeof irHash === 'string') {
    const irHashPattern = /const IR_HASH = '[^']*';/;
    source = source.replace(irHashPattern, `const IR_HASH = '${irHash}';`);
  }
  source = injectPipelineHelpers(source);
  await writeFile(runPath, source);
}

function injectPipelineHelpers(source) {
  const importPattern = "import inmem from './runtime/inmem.mjs';";
  if (!source.includes(importPattern)) {
    throw new Error('pilot-full-build-run: expected inmem import in run.mjs');
  }
  source = source.replace(
    importPattern,
    "import { createInmemRuntime } from './runtime/inmem.mjs';\nimport { createInmemAdapters } from './adapters/inmem.mjs';",
  );
  source = source.replace(
    "import { fileURLToPath } from 'node:url';",
    "import { fileURLToPath, pathToFileURL } from 'node:url';",
  );

  const helperLines = [
    "const PLACEHOLDERS = {",
    "  FRAMES: '__PILOT_FULL::FRAMES__',",
    "  MOMENTUM: '__PILOT_FULL::ORDERS_MOMENTUM__',",
    "  MEAN_REV: '__PILOT_FULL::ORDERS_MEAN_REVERSION__',",
    "  ORDERS: '__PILOT_FULL::ORDERS_COMBINED__',",
    "  RISK: '__PILOT_FULL::RISK__',",
    "  FILLS: '__PILOT_FULL::FILLS__',",
    "  STATE: '__PILOT_FULL::STATE__',",
    "  INITIAL: '__PILOT_FULL::INITIAL_STATE__',",
    "};",
    "",
    "function mapPlaceholders(irNode, replacements) {",
    "  if (!irNode || typeof irNode !== 'object') return;",
    "  if (Array.isArray(irNode)) {",
    "    for (const child of irNode) mapPlaceholders(child, replacements);",
    "    return;",
    "  }",
    "  if (irNode.node === 'Prim') {",
    "    const args = irNode.args ?? {};",
    "    if (typeof args.value === 'string' && replacements.has(args.value)) {",
    "      args.value = replacements.get(args.value);",
    "    }",
    "    if (typeof args.payload === 'string' && replacements.has(args.payload)) {",
    "      args.payload = replacements.get(args.payload);",
    "    }",
    "    irNode.args = args;",
    "  }",
    "  if (Array.isArray(irNode.children)) {",
    "    for (const child of irNode.children) mapPlaceholders(child, replacements);",
    "  }",
    "}",
    "",
    "async function loadPipelineArtifacts() {",
    "  const modulePath = process.env.TF_PILOT_PIPELINE;",
    "  const inputPath = process.env.TF_PILOT_INPUT;",
    "  if (!modulePath || !inputPath) {",
    "    throw new Error('pilot-full run requires TF_PILOT_PIPELINE and TF_PILOT_INPUT');",
    "  }",
    "  const { default: computePilotFullPipeline } = await import(pathToFileURL(modulePath).href);",
    "  const seed = Number(process.env.TF_PILOT_SEED ?? '42');",
    "  const slice = process.env.TF_PILOT_SLICE ?? '0:50:1';",
    "  return computePilotFullPipeline({ seed, slice, inputPath });",
    "}",
    "",
    "function createAdaptersWithPipeline(pipeline) {",
    "  const base = createInmemAdapters();",
    "  const replacements = new Map([",
    "    [PLACEHOLDERS.FRAMES, pipeline.framesNdjson],",
    "    [PLACEHOLDERS.MOMENTUM, pipeline.strategies.momentumNdjson],",
    "    [PLACEHOLDERS.MEAN_REV, pipeline.strategies.meanReversionNdjson],",
    "    [PLACEHOLDERS.ORDERS, pipeline.orders.combinedNdjson],",
    "    [PLACEHOLDERS.RISK, pipeline.risk.ndjson],",
    "    [PLACEHOLDERS.FILLS, pipeline.fills.ndjson],",
    "    [PLACEHOLDERS.STATE, pipeline.state.json + '\\n'],",
    "  ]);",
    "  return {",
    "    ...base,",
    "    async publish(topic, key, payload) {",
    "      const actual = replacements.get(payload) ?? payload;",
    "      await base.publish(topic, key, actual);",
    "    },",
    "    async writeObject(uri, key, value, idempotencyKey) {",
    "      const actual = replacements.get(value) ?? value;",
    "      await base.writeObject(uri, key, actual, idempotencyKey);",
    "    },",
    "    async readObject(uri, key) {",
    "      if (uri === 'res://pilot-full/state' && key === 'initial.json') {",
    "        return pipeline.state.initialJson + '\\n';",
    "      }",
    "      if (typeof base.readObject === 'function') {",
    "        return base.readObject(uri, key);",
    "      }",
    "      return null;",
    "    },",
    "  };",
    "}",
  ];

  const helperBlock = helperLines.join('\n');
  const helperInsertPoint = "const CATALOG_HASH =";
  if (!source.includes(helperInsertPoint)) {
    throw new Error('pilot-full-build-run: unable to locate helper insertion point');
  }
  source = source.replace(helperInsertPoint, `${helperBlock}\n${helperInsertPoint}`);

  const executionPattern = 'const execution = await runIR(ir, inmem, { traceMeta, provenance: provenanceBase });';
  if (!source.includes(executionPattern)) {
    throw new Error('pilot-full-build-run: expected runIR invocation');
  }
  const replacementLines = [
    'const pipeline = await loadPipelineArtifacts();',
    'const adapters = createAdaptersWithPipeline(pipeline);',
    'const runtime = createInmemRuntime({ adapters });',
    'mapPlaceholders(ir, new Map([',
    "  [PLACEHOLDERS.FRAMES, pipeline.framesNdjson],",
    "  [PLACEHOLDERS.MOMENTUM, pipeline.strategies.momentumNdjson],",
    "  [PLACEHOLDERS.MEAN_REV, pipeline.strategies.meanReversionNdjson],",
    "  [PLACEHOLDERS.ORDERS, pipeline.orders.combinedNdjson],",
    "  [PLACEHOLDERS.RISK, pipeline.risk.ndjson],",
    "  [PLACEHOLDERS.FILLS, pipeline.fills.ndjson],",
    "  [PLACEHOLDERS.STATE, pipeline.state.json + '\\n'],",
    ']));',
    'const execution = await runIR(ir, runtime, { traceMeta, provenance: provenanceBase });',
    'const snapshotPath = process.env.TF_STORAGE_SNAPSHOT_PATH;',
    'if (snapshotPath) {',
    "  const snapshot = typeof runtime.getStorageSnapshot === 'function' ? runtime.getStorageSnapshot() : null;",
    '  if (snapshot) {',
    "    await writeFile(snapshotPath, JSON.stringify(snapshot, null, 2) + '\\n', 'utf8');",
    '  }',
    '}',
  ];
  const replacementBlock = replacementLines.join('\n    ');
  source = source.replace(executionPattern, replacementBlock);

  return source;
}

async function ensureDirs() {
  await rm(outDir, { recursive: true, force: true });
  await mkdir(outDir, { recursive: true });
  await mkdir(codegenDir, { recursive: true });
}

async function main() {
  await ensureDirs();

  const irPath = join(outDir, 'pilot_full.ir.json');
  const canonPath = join(outDir, 'pilot_full.canon.json');
  const manifestPath = join(outDir, 'pilot_full.manifest.json');

  sh('node', [tfCompose, 'parse', flowPath, '-o', irPath]);
  sh('node', [tfCompose, 'canon', flowPath, '-o', canonPath]);
  sh('node', [tfManifest, flowPath, '-o', manifestPath]);
  const manifest = await rewriteManifest(manifestPath);

  sh('node', [tfCompose, 'emit', '--lang', 'ts', flowPath, '--out', codegenDir]);
  const irRaw = await readFile(irPath, 'utf8');
  const irHash = sha256OfCanonicalJson(JSON.parse(irRaw));
  const manifestHash = await hashJsonLike(manifestPath);
  await patchRunFile(join(codegenDir, 'run.mjs'), manifest, manifestHash, irHash);

  const caps = {
    effects: ['Storage.Read', 'Storage.Write', 'Network.Out', 'Observability', 'Pure'],
    allow_writes_prefixes: ['res://pilot-full/'],
  };
  await writeFile(join(codegenDir, 'caps.json'), JSON.stringify(caps, null, 2) + '\n');

  await writeFile(join(outDir, 'catalog.json'), await readFile(specCatalogPath, 'utf8'));

  const statusPath = join(outDir, 'status.json');
  const tracePath = join(outDir, 'trace.jsonl');
  const summaryPath = join(outDir, 'summary.json');
  const storagePath = join(outDir, 'storage.json');

  await rm(statusPath, { recursive: true, force: true });
  await rm(tracePath, { recursive: true, force: true });
  await rm(summaryPath, { recursive: true, force: true });
  await rm(storagePath, { recursive: true, force: true });

  const env = {
    ...baseEnv,
    TF_STATUS_PATH: statusPath,
    TF_TRACE_PATH: tracePath,
    TF_PILOT_PIPELINE: pipelineModule,
    TF_PILOT_SEED: String(SEED),
    TF_PILOT_SLICE: SLICE,
    TF_PILOT_INPUT: INPUT_CSV,
    TF_STORAGE_SNAPSHOT_PATH: storagePath,
  };

  sh('node', [join(codegenDir, 'run.mjs'), '--caps', join(codegenDir, 'caps.json')], { env });

  const traceRaw = await readFile(tracePath, 'utf8');
  if (!traceRaw.trim()) {
    throw new Error('pilot-full-build-run: empty trace output');
  }
  const status = JSON.parse(await readFile(statusPath, 'utf8'));
  if (status.ok !== true) throw new Error('pilot-full-build-run: status.ok must be true');
  if (!Number.isFinite(status.ops) || status.ops < 2) throw new Error('pilot-full-build-run: status.ops too low');
  status.manifest_path = manifestPath;
  await writeFile(statusPath, JSON.stringify(status, null, 2) + '\n');

  const summaryProc = spawnSync('node', [traceSummary], {
    input: traceRaw,
    encoding: 'utf8',
    env: baseEnv,
  });
  if (summaryProc.status !== 0) {
    throw new Error('pilot-full-build-run: trace-summary failed');
  }
  const summaryJson = JSON.parse(summaryProc.stdout);
  const canonicalSummary = canonicalStringify(summaryJson);
  await writeFile(summaryPath, canonicalSummary + '\n');

  const storageSnapshot = JSON.parse(await readFile(storagePath, 'utf8'));
  await materializeArtifacts(storageSnapshot);

  const digests = {
    status: await hashJsonLike(statusPath),
    trace: await hashJsonLike(tracePath),
    summary: await hashJsonLike(summaryPath),
    storage: await hashJsonLike(storagePath),
    frames: await hashJsonLike(join(outDir, 'frames.ndjson')),
    orders: await hashJsonLike(join(outDir, 'orders.ndjson')),
    fills: await hashJsonLike(join(outDir, 'fills.ndjson')),
    state: await hashJsonLike(join(outDir, 'state.json')),
    risk: await hashJsonLike(join(outDir, 'risk.ndjson')),
    ir: await hashJsonLike(irPath),
    canon: await hashJsonLike(canonPath),
    manifest: await hashJsonLike(manifestPath),
  };
  await writeFile(join(outDir, 'digests.json'), JSON.stringify(digests, null, 2) + '\n');

  console.log('pilot-full-build-run: completed artifacts in', outDir);
}

async function materializeArtifacts(snapshot) {
  if (!snapshot || typeof snapshot !== 'object') {
    throw new Error('pilot-full-build-run: missing storage snapshot');
  }
  const mapping = [
    ['res://pilot-full/replay', 'frames.ndjson', 'frames.ndjson'],
    ['res://pilot-full/orders', 'combined.ndjson', 'orders.ndjson'],
    ['res://pilot-full/fills', 'fills.ndjson', 'fills.ndjson'],
    ['res://pilot-full/state', 'state.json', 'state.json'],
    ['res://pilot-full/risk', 'metrics.ndjson', 'risk.ndjson'],
  ];
  for (const [uri, key, fileName] of mapping) {
    const bucket = snapshot[uri];
    if (!bucket || typeof bucket !== 'object' || !(key in bucket)) {
      throw new Error(`pilot-full-build-run: snapshot missing ${uri}#${key}`);
    }
    const targetPath = join(outDir, fileName);
    await writeFile(targetPath, bucket[key], 'utf8');
  }
}

main().catch((err) => {
  console.error(err?.stack || err?.message || String(err));
  process.exitCode = 1;
});
