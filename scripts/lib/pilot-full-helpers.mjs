import { join, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';

import { replay } from '../../packages/pilot-replay/dist/index.js';
import { runStrategy } from '../../packages/pilot-strategy/dist/index.js';
import { createRisk } from '../../packages/pilot-risk/dist/index.js';
import { assertValidState, canonFrame, canonOrder } from '../../packages/pilot-core/dist/index.js';

import {
  absDecimal,
  addDecimal,
  decimalToString,
  multiplyDecimal,
  negateDecimal,
  parseDecimal,
  zeroDecimal,
} from './decimal.mjs';

const moduleDir = fileURLToPath(new URL('.', import.meta.url));
const repoRoot = resolve(moduleDir, '..', '..');
const defaultInput = join(repoRoot, 'tests', 'data', 'ticks-mini.csv');

export function resolveConfig(rawConfig = {}) {
  const config = {
    input: typeof rawConfig.input === 'string' && rawConfig.input.trim().length > 0
      ? rawConfig.input.trim()
      : defaultInput,
    seed: Number.isFinite(rawConfig.seed) ? Number(rawConfig.seed) : 42,
    slice: typeof rawConfig.slice === 'string' ? rawConfig.slice : '0:50:1',
    strategies: Array.isArray(rawConfig.strategies) && rawConfig.strategies.length > 0
      ? rawConfig.strategies.map(String)
      : ['momentum', 'meanReversion'],
    risk: typeof rawConfig.risk === 'object' && rawConfig.risk
      ? { ...rawConfig.risk }
      : { mode: 'exposure' },
  };
  if (!config.strategies.every((name) => name === 'momentum' || name === 'meanReversion')) {
    throw new Error('pilot-full: unsupported strategy requested');
  }
  return config;
}

export function ensureAbsolutePath(pathInput) {
  if (typeof pathInput !== 'string' || pathInput.trim().length === 0) {
    return defaultInput;
  }
  const trimmed = pathInput.trim();
  if (trimmed.startsWith('/')) {
    return trimmed;
  }
  return resolve(repoRoot, trimmed);
}

export function replayFrames(config) {
  const inputPath = ensureAbsolutePath(config.input);
  const result = replay({ input: inputPath, seed: config.seed, slice: config.slice });
  return result.frames.map((frame) => canonFrame(frame));
}

export function runStrategies(config, frames) {
  const orders = [];
  for (const strategyName of config.strategies) {
    const { orders: rawOrders } = runStrategy(
      { strategy: strategyName, framesPath: '', seed: config.seed },
      frames,
    );
    for (const order of rawOrders) {
      const canonical = canonOrder(order);
      const meta = { ...(canonical.meta ?? {}), strategy: strategyName };
      orders.push({ ...canonical, meta });
    }
  }
  orders.sort((a, b) => {
    if (a.ts !== b.ts) return a.ts - b.ts;
    if (a.sym !== b.sym) return a.sym < b.sym ? -1 : 1;
    return a.id < b.id ? -1 : a.id > b.id ? 1 : 0;
  });
  return orders;
}

export function evaluateRisk(config, orders, frames) {
  const riskConfig = config.risk && typeof config.risk === 'object' ? config.risk : { mode: 'exposure' };
  const risk = createRisk(riskConfig);
  const { metrics } = risk.evaluate(orders, frames);
  return metrics;
}

function buildFrameLookup(frames) {
  const lookup = new Map();
  for (const frame of frames) {
    if (!lookup.has(frame.sym)) {
      lookup.set(frame.sym, []);
    }
    lookup.get(frame.sym).push(frame);
  }
  for (const [sym, series] of lookup) {
    series.sort((a, b) => a.ts - b.ts || a.seq - b.seq);
    lookup.set(sym, series);
  }
  return lookup;
}

function lookupFramePrice(order, lookup) {
  const series = lookup.get(order.sym) ?? [];
  let candidate;
  for (const frame of series) {
    if (frame.ts <= order.ts) {
      candidate = frame;
    } else {
      break;
    }
  }
  const fallback = candidate ?? series[series.length - 1];
  if (!fallback) {
    throw new Error(`pilot-full: unable to locate frame for ${order.id}`);
  }
  return parseDecimal(fallback.last);
}

export function simulateFills(orders, frames) {
  const lookup = buildFrameLookup(frames);
  const fills = [];
  for (const order of orders) {
    const priceDecimal = order.price ? parseDecimal(order.price) : lookupFramePrice(order, lookup);
    const qtyDecimal = parseDecimal(order.quantity);
    const notional = multiplyDecimal(absDecimal(qtyDecimal), priceDecimal);
    const fill = {
      id: `${order.id}-fill`,
      order_id: order.id,
      ts: order.ts,
      sym: order.sym,
      side: order.side,
      quantity: decimalToString(qtyDecimal),
      price: decimalToString(priceDecimal),
      notional: decimalToString(notional),
      meta: order.meta ?? {},
    };
    fills.push(fill);
  }
  fills.sort((a, b) => {
    if (a.ts !== b.ts) return a.ts - b.ts;
    if (a.sym !== b.sym) return a.sym < b.sym ? -1 : 1;
    return a.order_id < b.order_id ? -1 : a.order_id > b.order_id ? 1 : 0;
  });
  return fills;
}

export function computeState(config, fills) {
  const positions = new Map();
  let cash = zeroDecimal();
  for (const fill of fills) {
    const qty = parseDecimal(fill.quantity);
    const price = parseDecimal(fill.price);
    const notional = multiplyDecimal(qty, price);
    const signedQty = fill.side === 'buy' ? qty : negateDecimal(qty);
    const signedCash = fill.side === 'buy' ? negateDecimal(notional) : notional;
    const current = positions.get(fill.sym) ?? zeroDecimal();
    positions.set(fill.sym, addDecimal(current, signedQty));
    cash = addDecimal(cash, signedCash);
  }
  const positionsObj = {};
  for (const [sym, value] of positions.entries()) {
    positionsObj[sym] = decimalToString(value);
  }
  const state = {
    seed: config.seed,
    cash: decimalToString(cash),
    positions: positionsObj,
  };
  assertValidState(state);
  return state;
}

export function toNdjson(values) {
  if (!Array.isArray(values) || values.length === 0) {
    return '';
  }
  return values.map((entry) => JSON.stringify(entry)).join('\n') + '\n';
}

