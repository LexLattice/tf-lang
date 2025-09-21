import { mkdir, writeFile } from 'node:fs/promises';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';

import { createInmemRuntime } from '../../packages/tf-l0-codegen-ts/src/runtime/inmem.mjs';
import { createInmemAdapters } from '../../packages/tf-l0-codegen-ts/src/adapters/inmem.mjs';

import {
  computeState,
  evaluateRisk,
  replayFrames,
  resolveConfig,
  runStrategies,
  simulateFills,
  toNdjson,
} from './pilot-full-helpers.mjs';

const moduleDir = fileURLToPath(new URL('.', import.meta.url));
const repoRoot = resolve(moduleDir, '..', '..');

function resolveOutDir() {
  const env = process.env.PILOT_FULL_OUT_DIR;
  if (env && env.trim()) {
    return resolve(env);
  }
  return join(repoRoot, 'out', '0.4', 'pilot-full');
}

const outDir = resolveOutDir();

async function ensureDir(path) {
  await mkdir(dirname(path), { recursive: true });
}

async function writeText(path, content) {
  await ensureDir(path);
  await writeFile(path, content, 'utf8');
}

function parseArgs(value) {
  if (typeof value !== 'string') return {};
  if (!value) return {};
  try {
    return JSON.parse(value);
  } catch {
    return {};
  }
}

function targetPath(key) {
  if (typeof key === 'string' && key.trim().length > 0) {
    return join(outDir, key);
  }
  return join(outDir, 'artifact');
}

const context = {
  config: resolveConfig(),
  frames: null,
  orders: null,
  metrics: null,
  fills: null,
  state: null,
};

async function handlePilotWrite(baseAdapters, uri, key, value, idempotencyKey) {
  if (uri === 'res://pilot-full/config') {
    const parsed = parseArgs(value);
    context.config = resolveConfig(parsed);
    return;
  }

  if (uri === 'res://pilot-full/replay') {
    context.frames = replayFrames(context.config);
    const framesPath = targetPath(key || 'frames.ndjson');
    const serialized = toNdjson(context.frames);
    if (serialized) {
      await writeText(framesPath, serialized);
    } else {
      await writeText(framesPath, '');
    }
    return;
  }

  if (uri === 'res://pilot-full/strategy') {
    if (!context.frames) {
      throw new Error('pilot-full-runtime: replay stage must run before strategy');
    }
    context.orders = runStrategies(context.config, context.frames);
    const ordersPath = targetPath(key || 'orders.ndjson');
    const serialized = toNdjson(context.orders);
    if (serialized) {
      await writeText(ordersPath, serialized);
    } else {
      await writeText(ordersPath, '');
    }
    return;
  }

  if (uri === 'res://pilot-full/risk') {
    if (!context.orders || !context.frames) {
      throw new Error('pilot-full-runtime: strategy stage must run before risk');
    }
    context.metrics = evaluateRisk(context.config, context.orders, context.frames);
    const metricsPath = targetPath(key || 'metrics.ndjson');
    const serialized = toNdjson(context.metrics);
    if (serialized) {
      await writeText(metricsPath, serialized);
    } else {
      await writeText(metricsPath, '');
    }
    return;
  }

  if (uri === 'res://pilot-full/exec') {
    if (!context.orders || !context.frames) {
      throw new Error('pilot-full-runtime: strategy stage must run before exec');
    }
    context.fills = simulateFills(context.orders, context.frames);
    const fillsPath = targetPath(key || 'fills.ndjson');
    const serialized = toNdjson(context.fills);
    if (serialized) {
      await writeText(fillsPath, serialized);
    } else {
      await writeText(fillsPath, '');
    }
    return;
  }

  if (uri === 'res://pilot-full/ledger') {
    if (!context.fills) {
      throw new Error('pilot-full-runtime: exec stage must run before ledger');
    }
    context.state = computeState(context.config, context.fills);
    const statePath = targetPath(key || 'state.json');
    await writeText(statePath, JSON.stringify(context.state, null, 2) + '\n');
    return;
  }

  await baseAdapters.writeObject(uri, key, value, idempotencyKey);
}

const baseAdapters = createInmemAdapters();

const adapters = {
  ...baseAdapters,
  writeObject: async (uri, key, value, idempotencyKey) => {
    if (typeof uri === 'string' && uri.startsWith('res://pilot-full/')) {
      await handlePilotWrite(baseAdapters, uri, key, value, idempotencyKey);
      return;
    }
    await baseAdapters.writeObject(uri, key, value, idempotencyKey);
  },
};

const runtime = createInmemRuntime({ adapters });

export default runtime;
export { context as pilotFullContext, outDir as pilotFullOutDir };

