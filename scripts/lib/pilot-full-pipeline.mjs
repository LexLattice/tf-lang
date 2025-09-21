#!/usr/bin/env node
import { join, dirname } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';

const here = dirname(fileURLToPath(import.meta.url));
const rootDir = join(here, '..', '..');
const defaultInput = join(rootDir, 'tests', 'data', 'ticks-mini.csv');

let cachedDeps = null;
let canonNumberRef = null;

async function loadDependencies() {
  if (cachedDeps) return cachedDeps;
  const replayMod = await import(pathToFileURL(join(rootDir, 'packages', 'pilot-replay', 'dist', 'index.js')).href);
  const strategyMod = await import(pathToFileURL(join(rootDir, 'packages', 'pilot-strategy', 'dist', 'index.js')).href);
  const riskMod = await import(pathToFileURL(join(rootDir, 'packages', 'pilot-risk', 'dist', 'index.js')).href);
  const coreMod = await import(pathToFileURL(join(rootDir, 'packages', 'pilot-core', 'dist', 'index.js')).href);
  canonNumberRef = coreMod.canonNumber;
  cachedDeps = {
    runReplay: replayMod.replay,
    runStrategy: strategyMod.runStrategy,
    createRisk: riskMod.createRisk,
  };
  return cachedDeps;
}

function toNdjson(list) {
  if (!Array.isArray(list) || list.length === 0) {
    return '';
  }
  return list.map((item) => JSON.stringify(item)).join('\n') + '\n';
}

function decimalFromString(input) {
  if (typeof canonNumberRef !== 'function') {
    throw new Error('pilot pipeline: canonNumber not loaded');
  }
  const canonical = canonNumberRef(input);
  const negative = canonical.startsWith('-');
  const body = negative ? canonical.slice(1) : canonical;
  const [intPart, fracPart = ''] = body.split('.', 2);
  const digits = `${intPart}${fracPart}`.replace(/^0+(?=\d)/, '');
  const value = digits.length ? BigInt(digits) : 0n;
  return { value: negative ? -value : value, scale: fracPart.length };
}

function alignScale(decimal, targetScale) {
  if (decimal.scale === targetScale) {
    return decimal;
  }
  if (decimal.scale > targetScale) {
    throw new Error('alignScale cannot reduce precision');
  }
  const factor = 10n ** BigInt(targetScale - decimal.scale);
  return { value: decimal.value * factor, scale: targetScale };
}

function addDecimal(a, b) {
  const scale = Math.max(a.scale, b.scale);
  const aAligned = alignScale(a, scale);
  const bAligned = alignScale(b, scale);
  return { value: aAligned.value + bAligned.value, scale };
}

function subtractDecimal(a, b) {
  const scale = Math.max(a.scale, b.scale);
  const aAligned = alignScale(a, scale);
  const bAligned = alignScale(b, scale);
  return { value: aAligned.value - bAligned.value, scale };
}

function multiplyDecimal(a, b) {
  return { value: a.value * b.value, scale: a.scale + b.scale };
}

function negateDecimal(decimal) {
  return { value: -decimal.value, scale: decimal.scale };
}

function absDecimal(decimal) {
  return decimal.value < 0n ? negateDecimal(decimal) : decimal;
}

function decimalToString(decimal) {
  const negative = decimal.value < 0n;
  const absolute = negative ? -decimal.value : decimal.value;
  let digits = absolute.toString();
  if (decimal.scale === 0) {
    const intPart = digits.replace(/^0+(?=\d)/, '');
    const canonicalInt = intPart.length > 0 ? intPart : '0';
    return negative ? `-${canonicalInt}` : canonicalInt;
  }
  if (digits.length <= decimal.scale) {
    digits = digits.padStart(decimal.scale + 1, '0');
  }
  const intPartRaw = digits.slice(0, digits.length - decimal.scale) || '0';
  const fracPartRaw = digits.slice(digits.length - decimal.scale).replace(/0+$/, '');
  const intPart = intPartRaw.replace(/^0+(?=\d)/, '') || '0';
  if (fracPartRaw.length === 0) {
    return negative ? `-${intPart}` : intPart;
  }
  return `${negative ? '-' : ''}${intPart}.${fracPartRaw}`;
}

function zeroDecimal() {
  return { value: 0n, scale: 0 };
}

function buildFrameLookup(frames) {
  const lookup = new Map();
  for (const frame of frames) {
    if (!lookup.has(frame.sym)) {
      lookup.set(frame.sym, []);
    }
    lookup.get(frame.sym).push(frame);
  }
  for (const series of lookup.values()) {
    series.sort((a, b) => a.ts - b.ts);
  }
  return lookup;
}

function findFramePrice(order, lookup) {
  const series = lookup.get(order.sym) ?? [];
  let candidate = null;
  for (const frame of series) {
    if (frame.ts <= order.ts) {
      candidate = frame;
    } else {
      break;
    }
  }
  return candidate ?? series[series.length - 1] ?? null;
}

function computeFillsAndState(orders, frames, seed) {
  const sorted = [...orders].sort((a, b) => {
    if (a.ts !== b.ts) return a.ts - b.ts;
    if (a.sym !== b.sym) return a.sym < b.sym ? -1 : 1;
    return a.id < b.id ? -1 : a.id > b.id ? 1 : 0;
  });
  const lookup = buildFrameLookup(frames);
  const fills = [];
  const positions = new Map();
  let cash = zeroDecimal();
  for (const order of sorted) {
    const qty = decimalFromString(order.quantity);
    const signedQty = order.side === 'buy' ? qty : negateDecimal(qty);
    const priceDecimal = order.price ? decimalFromString(order.price) : (() => {
      const frame = findFramePrice(order, lookup);
      if (!frame) {
        throw new Error(`Unable to locate price for order ${order.id}`);
      }
      return decimalFromString(frame.last);
    })();
    const notional = multiplyDecimal(absDecimal(qty), priceDecimal);
    const symKey = order.sym;
    const prev = positions.get(symKey) ?? zeroDecimal();
    positions.set(symKey, addDecimal(prev, signedQty));
    cash = order.side === 'buy' ? subtractDecimal(cash, notional) : addDecimal(cash, notional);
    fills.push({
      id: `${order.id}-fill`,
      orderId: order.id,
      ts: order.ts,
      sym: order.sym,
      side: order.side,
      quantity: decimalToString(qty),
      price: decimalToString(priceDecimal),
      notional: decimalToString(notional),
    });
  }
  const positionsObject = {};
  const sortedSymbols = Array.from(positions.keys()).sort();
  for (const sym of sortedSymbols) {
    positionsObject[sym] = decimalToString(positions.get(sym));
  }
  const state = {
    seed,
    cash: decimalToString(cash),
    positions: positionsObject,
  };
  return { fills, state };
}

export async function computePilotFullPipeline(options = {}) {
  const { runReplay, runStrategy, createRisk } = await loadDependencies();
  const seed = Number.isFinite(Number(options.seed)) ? Number(options.seed) : 42;
  const slice = typeof options.slice === 'string' ? options.slice : '0:50:1';
  const inputPath = typeof options.inputPath === 'string' ? options.inputPath : defaultInput;

  const { frames } = runReplay({ input: inputPath, seed, slice });

  const momentum = runStrategy({ strategy: 'momentum', framesPath: '', seed }, frames).orders;
  const meanReversion = runStrategy({ strategy: 'meanReversion', framesPath: '', seed }, frames).orders;
  const combinedOrders = [...momentum, ...meanReversion].sort((a, b) => {
    if (a.ts !== b.ts) return a.ts - b.ts;
    if (a.sym !== b.sym) return a.sym < b.sym ? -1 : 1;
    return a.id < b.id ? -1 : a.id > b.id ? 1 : 0;
  });

  const riskEngine = createRisk({ mode: 'exposure' });
  const riskEvaluation = riskEngine.evaluate(combinedOrders, frames);

  const { fills, state } = computeFillsAndState(combinedOrders, frames, seed);
  const initialState = { seed, cash: '0', positions: {} };

  return {
    seed,
    slice,
    frames,
    framesNdjson: toNdjson(frames),
    strategies: {
      momentum,
      meanReversion,
      momentumNdjson: toNdjson(momentum),
      meanReversionNdjson: toNdjson(meanReversion),
    },
    orders: {
      combined: combinedOrders,
      combinedNdjson: toNdjson(combinedOrders),
    },
    risk: {
      metrics: riskEvaluation.metrics,
      ndjson: toNdjson(riskEvaluation.metrics),
    },
    fills: {
      list: fills,
      ndjson: toNdjson(fills),
    },
    state: {
      initial: initialState,
      final: state,
      json: JSON.stringify(state, null, 2),
      initialJson: JSON.stringify(initialState, null, 2),
    },
  };
}

export default computePilotFullPipeline;
