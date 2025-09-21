#!/usr/bin/env node
import { join, dirname } from 'node:path';
import { fileURLToPath } from 'node:url';

import {
  replay,
  loadCsvFrames,
  applySlice,
} from '../packages/pilot-replay/dist/index.js';
import {
  runStrategy,
} from '../packages/pilot-strategy/dist/index.js';
import {
  createRisk,
} from '../packages/pilot-risk/dist/index.js';
import {
  canonNumber,
} from '../packages/pilot-core/dist/index.js';

const here = dirname(fileURLToPath(import.meta.url));
const rootDir = join(here, '..');

const DEFAULT_SCALE = 8;
const SCALE_FACTOR = 10n ** BigInt(DEFAULT_SCALE);

function zeroDecimal() {
  return { value: 0n, scale: 0 };
}

function parseDecimal(input) {
  const canonical = canonNumber(input);
  const negative = canonical.startsWith('-');
  const body = negative ? canonical.slice(1) : canonical;
  const [intPart, fracPart = ''] = body.split('.', 2);
  const digits = `${intPart}${fracPart}`;
  const scale = fracPart.length;
  const bigintValue = BigInt(digits.length === 0 ? '0' : digits);
  return {
    value: negative ? -bigintValue : bigintValue,
    scale,
  };
}

function alignScale(decimal, targetScale) {
  if (decimal.scale === targetScale) {
    return { value: decimal.value, scale: targetScale };
  }
  if (decimal.scale < targetScale) {
    const factor = 10n ** BigInt(targetScale - decimal.scale);
    return { value: decimal.value * factor, scale: targetScale };
  }
  const divisor = 10n ** BigInt(decimal.scale - targetScale);
  return {
    value: decimal.value / divisor,
    scale: targetScale,
  };
}

function addDecimal(left, right) {
  const scale = Math.max(left.scale, right.scale);
  const a = alignScale(left, scale);
  const b = alignScale(right, scale);
  return { value: a.value + b.value, scale };
}

function negateDecimal(value) {
  return { value: -value.value, scale: value.scale };
}

function subtractDecimal(left, right) {
  return addDecimal(left, negateDecimal(right));
}

function multiplyDecimal(left, right) {
  return {
    value: left.value * right.value,
    scale: left.scale + right.scale,
  };
}

function decimalToString(decimal) {
  const { value, scale } = decimal;
  if (scale === 0) {
    return value.toString();
  }
  const negative = value < 0n;
  let abs = negative ? -value : value;
  const base = 10n ** BigInt(scale);
  const intPart = abs / base;
  const fracPart = abs % base;
  let fracStr = fracPart.toString().padStart(scale, '0');
  fracStr = fracStr.replace(/0+$/, '');
  let result = intPart.toString();
  if (fracStr.length > 0) {
    result += `.${fracStr}`;
  }
  if (negative && result !== '0') {
    result = `-${result}`;
  }
  return result;
}

function buildFrameLookup(frames) {
  const map = new Map();
  for (const frame of frames) {
    if (!map.has(frame.sym)) {
      map.set(frame.sym, []);
    }
    map.get(frame.sym).push(frame);
  }
  for (const list of map.values()) {
    list.sort((a, b) => a.ts - b.ts);
  }
  return map;
}

function lookupFramePrice(order, lookup) {
  const series = lookup.get(order.sym) ?? [];
  let candidate = null;
  for (const frame of series) {
    if (frame.ts <= order.ts) {
      candidate = frame;
    } else {
      break;
    }
  }
  const resolved = candidate ?? series[series.length - 1];
  if (!resolved) {
    throw new Error(`Unable to resolve price for order ${order.id}`);
  }
  return parseDecimal(resolved.last);
}

export function runReplay({ inputPath, seed, slice }) {
  if (!inputPath) {
    throw new Error('runReplay: inputPath required');
  }
  const frames = replay({ input: inputPath, seed, slice }).frames;
  return frames;
}

export function loadReplayCsv({ inputPath, seed, slice }) {
  const frames = loadCsvFrames(inputPath);
  const sliced = applySlice(frames, slice);
  return sliced.map((frame) => ({ ...frame, ts: Number(frame.ts) }));
}

export function runStrategyOrders(strategy, frames, seed, framesPath = '') {
  const name = strategy;
  if (name !== 'momentum' && name !== 'meanReversion') {
    throw new Error(`Unsupported strategy: ${strategy}`);
  }
  const result = runStrategy({ strategy: name, framesPath, seed }, frames);
  return [...result.orders].sort((a, b) => {
    if (a.ts !== b.ts) return a.ts - b.ts;
    if (a.sym !== b.sym) return a.sym < b.sym ? -1 : 1;
    return a.id < b.id ? -1 : a.id > b.id ? 1 : 0;
  });
}

export function combineOrders(momentumOrders, meanReversionOrders) {
  const combined = [...momentumOrders, ...meanReversionOrders];
  combined.sort((a, b) => {
    if (a.ts !== b.ts) return a.ts - b.ts;
    if (a.sym !== b.sym) return a.sym < b.sym ? -1 : 1;
    return a.id < b.id ? -1 : a.id > b.id ? 1 : 0;
  });
  return combined;
}

export function evaluateRiskMetrics(frames, orders) {
  const risk = createRisk({ mode: 'exposure' });
  const evaluation = risk.evaluate(orders, frames);
  const metrics = evaluation.metrics.map((entry) => ({
    sym: entry.sym,
    grossNotional: entry.grossNotional,
    netQty: entry.netQty,
    maxAbsExposure: entry.maxAbsExposure,
    orders: entry.orders,
  }));
  metrics.sort((a, b) => (a.sym < b.sym ? -1 : a.sym > b.sym ? 1 : 0));
  return metrics;
}

export function deriveFillsAndState(frames, orders, seed) {
  const lookup = buildFrameLookup(frames);
  const fills = [];
  for (const order of orders) {
    const quantity = canonNumber(order.quantity);
    const basePrice = order.price ? canonNumber(order.price) : decimalToString(lookupFramePrice(order, lookup));
    fills.push({
      id: `fill-${order.id}`,
      order_id: order.id,
      ts: order.ts,
      sym: order.sym,
      side: order.side,
      quantity,
      price: basePrice,
      status: 'filled',
    });
  }

  fills.sort((a, b) => {
    if (a.ts !== b.ts) return a.ts - b.ts;
    if (a.sym !== b.sym) return a.sym < b.sym ? -1 : 1;
    return a.order_id < b.order_id ? -1 : a.order_id > b.order_id ? 1 : 0;
  });

  const positionAcc = new Map();
  let cash = zeroDecimal();

  for (const fill of fills) {
    const qtyDecimal = parseDecimal(fill.quantity);
    const priceDecimal = parseDecimal(fill.price);
    const qtyScaled = alignScale(qtyDecimal, DEFAULT_SCALE);
    const priceScaled = alignScale(priceDecimal, DEFAULT_SCALE);
    const notionalRaw = multiplyDecimal(qtyScaled, priceScaled);
    const notional = {
      value: notionalRaw.value / SCALE_FACTOR,
      scale: DEFAULT_SCALE,
    };

    const signedQty = fill.side === 'sell' ? negateDecimal(qtyScaled) : qtyScaled;
    const existing = positionAcc.get(fill.sym) ?? zeroDecimal();
    positionAcc.set(fill.sym, addDecimal(existing, signedQty));

    cash = fill.side === 'sell' ? addDecimal(cash, notional) : subtractDecimal(cash, notional);
  }

  const positions = {};
  for (const [sym, value] of Array.from(positionAcc.entries()).sort((a, b) => (a[0] < b[0] ? -1 : a[0] > b[0] ? 1 : 0))) {
    const canonical = decimalToString(alignScale(value, DEFAULT_SCALE));
    if (canonical !== '0') {
      positions[sym] = canonical;
    }
  }

  const state = {
    seed,
    cash: decimalToString(alignScale(cash, DEFAULT_SCALE)),
    positions,
    meta: {
      fills: fills.length,
      strategies: ['momentum', 'meanReversion'],
      risk: 'exposure',
      scale: DEFAULT_SCALE,
    },
  };

  return { fills, state };
}

export function buildPilotArtifacts(options) {
  const { inputPath, seed, slice } = options;
  const frames = options.frames ?? runReplay({ inputPath, seed, slice });
  const strategies = options.strategies ?? {};
  const momentum = strategies.momentum ?? runStrategyOrders('momentum', frames, seed, inputPath ?? '');
  const meanReversion = strategies.meanReversion ?? runStrategyOrders('meanReversion', frames, seed, inputPath ?? '');
  const orders = combineOrders(momentum, meanReversion);
  const riskMetrics = evaluateRiskMetrics(frames, orders);
  const { fills, state } = deriveFillsAndState(frames, orders, seed);
  return {
    frames,
    strategies: { momentum, meanReversion },
    orders,
    riskMetrics,
    fills,
    state,
  };
}

export { rootDir };
