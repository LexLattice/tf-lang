import { createInmemRuntime } from '../../packages/tf-l0-codegen-ts/src/runtime/inmem.mjs';
import {
  DEFAULT_INPUT,
  DEFAULT_SLICE,
  DEFAULT_SEED,
  loadReplayFrames,
  runStrategyOrders,
  evaluateRiskMetrics,
  computeFills,
  computeLedgerState,
  collectPilotOutputs,
  toNdjson,
  toJson,
  combineOrders,
} from './pilot-full-support.mjs';

const STORAGE_PREFIX = 'res://pilot-full';

function ensureNumber(value, fallback) {
  if (typeof value === 'number' && Number.isFinite(value)) return value;
  const parsed = Number(value);
  if (Number.isFinite(parsed)) return parsed;
  return fallback;
}

function ensureString(value, fallback) {
  if (typeof value === 'string' && value.trim().length > 0) return value;
  return fallback;
}

export function createPilotFullRuntime(options = {}) {
  const base = createInmemRuntime(options);
  const baseGetAdapter = base.getAdapter.bind(base);
  const baseCanonicalPrim = base.canonicalPrim.bind(base);
  const baseEffectFor = base.effectFor.bind(base);

  const pilot = {
    seed: DEFAULT_SEED,
    input: DEFAULT_INPUT,
    slice: DEFAULT_SLICE,
    frames: [],
    momentumOrders: [],
    meanReversionOrders: [],
    riskMetrics: [],
    fills: [],
    state: null,
  };

  base.state.pilot = pilot;

  const custom = new Map();

  function register(name, effect, fn) {
    const handler = async (args = {}, ctx = base.state) => fn(args ?? {}, ctx ?? base.state);
    custom.set(name, { effect, handler });
  }

  register('pilot-replay', 'Storage.Read', async (args) => {
    pilot.input = ensureString(args.input, pilot.input);
    pilot.slice = ensureString(args.slice, pilot.slice);
    pilot.seed = ensureNumber(args.seed, pilot.seed);
    pilot.frames = loadReplayFrames({ input: pilot.input, slice: pilot.slice, seed: pilot.seed });
    return { ok: true };
  });

  register('pilot-strategy', 'Pure', async (args) => {
    const strategy = ensureString(args.strategy, 'momentum');
    const seed = ensureNumber(args.seed, pilot.seed);
    const params = typeof args.params === 'object' && args.params !== null ? args.params : {};
    const orders = runStrategyOrders(pilot.frames, seed, strategy, params);
    if (strategy && strategy.toLowerCase().startsWith('mean')) {
      pilot.meanReversionOrders = orders;
    } else {
      pilot.momentumOrders = orders;
    }
    return { ok: true };
  });

  register('pilot-risk', 'Pure', async (args) => {
    const mode = ensureString(args.mode, 'exposure');
    const combined = combineOrders(pilot.momentumOrders, pilot.meanReversionOrders);
    pilot.riskMetrics = evaluateRiskMetrics(combined, pilot.frames, mode);
    return { ok: true };
  });

  register('pilot-exec', 'Network.Out', async () => {
    const combined = combineOrders(pilot.momentumOrders, pilot.meanReversionOrders);
    pilot.fills = computeFills(combined, pilot.frames);
    const publish = baseGetAdapter('publish');
    if (typeof publish === 'function') {
      const payload = JSON.stringify({ orders: combined.map((order) => order.id), fills: pilot.fills.length });
      await publish({ topic: 'pilot.exec', key: 'orders', payload }, base.state);
    }
    return { ok: true };
  });

  register('pilot-ledger', 'Storage.Write', async () => {
    pilot.state = computeLedgerState(pilot.fills, pilot.seed);
    const writeObject = baseGetAdapter('write-object');
    if (typeof writeObject === 'function') {
      await writeObject({ uri: `${STORAGE_PREFIX}/frames`, key: 'frames.ndjson', value: toNdjson(pilot.frames) }, base.state);
      await writeObject({ uri: `${STORAGE_PREFIX}/orders`, key: 'orders.ndjson', value: toNdjson(combineOrders(pilot.momentumOrders, pilot.meanReversionOrders)) }, base.state);
      await writeObject({ uri: `${STORAGE_PREFIX}/fills`, key: 'fills.ndjson', value: toNdjson(pilot.fills) }, base.state);
      await writeObject({ uri: `${STORAGE_PREFIX}/state`, key: 'state.json', value: toJson(pilot.state) }, base.state);
    }
    return { ok: true };
  });

  const runtime = {
    ...base,
    adapters: { ...base.adapters },
    getAdapter(name) {
      if (custom.has(name)) {
        return custom.get(name).handler;
      }
      return baseGetAdapter(name);
    },
    canonicalPrim(name) {
      if (custom.has(name)) {
        return name;
      }
      return baseCanonicalPrim(name);
    },
    effectFor(name) {
      if (custom.has(name)) {
        return custom.get(name).effect;
      }
      return baseEffectFor(name);
    },
  };

  for (const [name, entry] of custom.entries()) {
    runtime.adapters[name] = entry.handler;
    runtime[name] = entry.handler;
  }

  runtime.state = base.state;

  runtime.getPilotOutputs = () => collectPilotOutputs({
    frames: pilot.frames,
    momentumOrders: pilot.momentumOrders,
    meanReversionOrders: pilot.meanReversionOrders,
    riskMetrics: pilot.riskMetrics,
    fills: pilot.fills,
    state: pilot.state,
  });

  return runtime;
}

export function extractPilotOutputs(runtime) {
  if (!runtime || !runtime.state || !runtime.state.pilot) {
    return null;
  }
  const pilot = runtime.state.pilot;
  return collectPilotOutputs({
    frames: pilot.frames,
    momentumOrders: pilot.momentumOrders,
    meanReversionOrders: pilot.meanReversionOrders,
    riskMetrics: pilot.riskMetrics,
    fills: pilot.fills,
    state: pilot.state,
  });
}
