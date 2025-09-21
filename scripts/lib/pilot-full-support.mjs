#!/usr/bin/env node
import { resolve } from 'node:path';

import { replay as runReplay } from '../../packages/pilot-replay/dist/index.js';
import { createRisk } from '../../packages/pilot-risk/dist/index.js';
import { createStrategy, STRATEGY_DEFAULTS } from '../../packages/pilot-strategy/dist/index.js';
import {
  canonNumber,
  canonOrder,
  canonFrame,
  assertValidState,
} from '../../packages/pilot-core/dist/index.js';

export const DEFAULT_INPUT = 'tests/data/ticks-mini.csv';
export const DEFAULT_SLICE = '0:50:1';
export const DEFAULT_SEED = 42;

function resolveInputPath(input) {
  const path = typeof input === 'string' && input.trim().length > 0 ? input : DEFAULT_INPUT;
  return resolve(process.cwd(), path);
}

export function loadReplayFrames({ input = DEFAULT_INPUT, slice = DEFAULT_SLICE, seed = DEFAULT_SEED } = {}) {
  const resolved = resolveInputPath(input);
  const { frames } = runReplay({ input: resolved, slice, seed });
  return frames.map((frame) => canonFrame(frame));
}

export function runStrategyOrders(frames, seed, name, params = {}) {
  if (!Array.isArray(frames)) {
    throw new TypeError('frames must be an array');
  }
  const strategyName = normalizeStrategyName(name);
  const config = {
    seed: Number.isFinite(seed) ? seed : DEFAULT_SEED,
    params: mergeStrategyParams(strategyName, params),
  };
  const strategy = createStrategy(strategyName, config);
  const state = { seed: config.seed, cash: '0', positions: {} };
  const orders = [];
  for (const frame of frames) {
    const produced = strategy.decide(state, frame) ?? [];
    for (const order of produced) {
      orders.push(canonOrder(order));
    }
  }
  return sortOrders(orders);
}

function mergeStrategyParams(name, overrides) {
  const defaults = STRATEGY_DEFAULTS[name];
  if (!overrides || typeof overrides !== 'object') {
    return defaults;
  }
  return { ...defaults, ...overrides };
}

function normalizeStrategyName(name) {
  if (!name) return 'momentum';
  const normalized = String(name).toLowerCase();
  if (normalized === 'momentum') return 'momentum';
  if (normalized === 'mean-reversion' || normalized === 'meanreversion' || normalized === 'mean_reversion') {
    return 'meanReversion';
  }
  throw new Error(`Unsupported strategy name: ${name}`);
}

export function combineOrders(...lists) {
  const merged = [];
  for (const list of lists) {
    if (Array.isArray(list)) {
      merged.push(...list);
    }
  }
  return sortOrders(merged);
}

export function sortOrders(orders) {
  return [...orders].sort((a, b) => {
    if (a.ts !== b.ts) return a.ts - b.ts;
    if (a.sym !== b.sym) return a.sym < b.sym ? -1 : 1;
    if (a.id !== b.id) return a.id < b.id ? -1 : 1;
    return 0;
  });
}

export function evaluateRiskMetrics(orders, frames, mode = 'exposure') {
  const context = createRisk({ mode });
  const result = context.evaluate(orders ?? [], frames ?? []);
  return Array.isArray(result.metrics) ? result.metrics : [];
}

export function computeFills(orders, frames) {
  const sortedOrders = sortOrders(orders ?? []);
  const frameLookup = buildFrameLookup(frames ?? []);
  const fills = [];
  for (const order of sortedOrders) {
    const quantity = canonNumber(order.quantity);
    const price = resolveOrderPrice(order, frameLookup);
    const notional = multiplyCanonical(quantity, price);
    fills.push({
      id: `${order.id}-fill`,
      order_id: order.id,
      ts: order.ts,
      sym: order.sym,
      side: order.side,
      quantity,
      price,
      notional,
    });
  }
  return fills;
}

export function computeLedgerState(fills, seed = DEFAULT_SEED) {
  const state = { seed: Number.isFinite(seed) ? seed : DEFAULT_SEED, cash: '0', positions: {} };
  for (const fill of fills ?? []) {
    const qty = parseDecimal(fill.quantity);
    const notional = parseDecimal(fill.notional);
    const sym = fill.sym;
    const current = parseDecimal(state.positions[sym] ?? '0');
    if (fill.side === 'sell') {
      const updatedCash = addDecimal(parseDecimal(state.cash), notional);
      const updatedPosition = subtractDecimal(current, qty);
      state.cash = decimalToString(updatedCash);
      state.positions[sym] = decimalToString(updatedPosition);
    } else {
      const updatedCash = subtractDecimal(parseDecimal(state.cash), notional);
      const updatedPosition = addDecimal(current, qty);
      state.cash = decimalToString(updatedCash);
      state.positions[sym] = decimalToString(updatedPosition);
    }
  }
  for (const key of Object.keys(state.positions)) {
    const value = decimalToString(parseDecimal(state.positions[key]));
    if (value === '0') {
      delete state.positions[key];
    } else {
      state.positions[key] = value;
    }
  }
  assertValidState(state);
  return state;
}

function buildFrameLookup(frames) {
  const map = new Map();
  for (const frame of frames) {
    if (!map.has(frame.sym)) {
      map.set(frame.sym, []);
    }
    map.get(frame.sym).push(frame);
  }
  for (const series of map.values()) {
    series.sort((a, b) => a.ts - b.ts);
  }
  return map;
}

function resolveOrderPrice(order, frameLookup) {
  if (order.price !== undefined && order.price !== null) {
    return canonNumber(order.price);
  }
  const series = frameLookup.get(order.sym) ?? [];
  let candidate = null;
  for (const frame of series) {
    if (frame.ts <= order.ts) {
      candidate = frame;
    } else {
      break;
    }
  }
  const fallback = candidate ?? series[series.length - 1];
  if (!fallback) {
    throw new Error(`Unable to resolve price for order ${order.id}`);
  }
  return canonNumber(fallback.last);
}

function multiplyCanonical(a, b) {
  const left = parseDecimal(a);
  const right = parseDecimal(b);
  const product = multiplyDecimal(left, right);
  return decimalToString(product);
}

function parseDecimal(value) {
  const canonical = canonNumber(value ?? '0');
  const negative = canonical.startsWith('-');
  const body = negative ? canonical.slice(1) : canonical;
  const [intPart, fracPart = ''] = body.split('.', 2);
  const digits = `${intPart}${fracPart}`.replace(/^0+(?=\d)/, '');
  const scale = fracPart.length;
  const magnitude = digits.length === 0 ? 0n : BigInt(digits);
  return { value: negative ? -magnitude : magnitude, scale };
}

function alignScale(decimal, targetScale) {
  if (decimal.scale === targetScale) {
    return decimal;
  }
  const diff = targetScale - decimal.scale;
  if (diff < 0) {
    return { value: decimal.value, scale: decimal.scale };
  }
  const factor = 10n ** BigInt(diff);
  return { value: decimal.value * factor, scale: targetScale };
}

function addDecimal(a, b) {
  const scale = Math.max(a.scale, b.scale);
  const left = alignScale(a, scale);
  const right = alignScale(b, scale);
  return { value: left.value + right.value, scale };
}

function subtractDecimal(a, b) {
  const scale = Math.max(a.scale, b.scale);
  const left = alignScale(a, scale);
  const right = alignScale(b, scale);
  return { value: left.value - right.value, scale };
}

function multiplyDecimal(a, b) {
  return { value: a.value * b.value, scale: a.scale + b.scale };
}

function decimalToString(decimal) {
  const { value, scale } = decimal;
  if (scale === 0) {
    return value.toString();
  }
  const negative = value < 0n;
  const magnitude = negative ? -value : value;
  const digits = magnitude.toString().padStart(scale + 1, '0');
  const intPart = digits.slice(0, digits.length - scale).replace(/^0+(?=\d)/, '');
  const fracPart = digits.slice(digits.length - scale).replace(/0+$/, '');
  const integer = intPart.length === 0 ? '0' : intPart;
  const fractional = fracPart.length === 0 ? '' : `.${fracPart}`;
  const result = `${negative ? '-' : ''}${integer}${fractional}`;
  return result === '-0' ? '0' : result;
}

export function toNdjson(items) {
  const lines = (items ?? []).map((item) => JSON.stringify(item));
  return lines.join('\n') + (lines.length ? '\n' : '');
}

export function toJson(value) {
  return JSON.stringify(value, null, 2) + '\n';
}

export function collectPilotOutputs({ frames, momentumOrders, meanReversionOrders, riskMetrics, fills, state }) {
  const combinedOrders = combineOrders(momentumOrders, meanReversionOrders);
  return {
    frames,
    momentumOrders,
    meanReversionOrders,
    orders: combinedOrders,
    riskMetrics: riskMetrics ?? [],
    fills: fills ?? [],
    state,
  };
}
