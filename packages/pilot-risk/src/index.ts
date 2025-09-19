import { readFileSync, writeFileSync } from 'node:fs';
import { dirname, resolve } from 'node:path';
import { mkdirSync } from 'node:fs';
import { fileURLToPath } from 'node:url';

import Ajv, { ValidateFunction } from 'ajv';

import {
  Frame,
  Order,
  State,
  assertValidFrame,
  assertValidOrder,
  canonNumber,
  toMinorUnits,
} from '@tf-lang/pilot-core';

import configSchema from './schemas/config.schema.json' with { type: 'json' };

export interface RiskConfig {
  mode: 'exposure';
  meta?: Record<string, unknown>;
}

export interface RiskContext {
  evaluate(state: State, orders: Order[], frame: Frame): Order[];
}

export interface RiskEvaluation {
  sym: string;
  orderCount: number;
  grossNotional: string;
  netQuantity: string;
  maxAbsExposure: string;
}

export interface EvaluateOptions {
  orders: Order[];
  frames: Frame[];
}

export interface EvaluateFromPathsOptions {
  ordersPath: string;
  framesPath: string;
}

const ajv = new Ajv({ allErrors: true, strict: false });
const validateConfig: ValidateFunction<RiskConfig> = ajv.compile<RiskConfig>(configSchema as any);

export function createRisk(config: unknown): RiskContext {
  if (!validateConfig(config)) {
    throw new Error(ajv.errorsText(validateConfig.errors));
  }
  return {
    evaluate(_state: State, orders: Order[]): Order[] {
      return orders;
    },
  };
}

export function evaluateRisk(options: EvaluateOptions): RiskEvaluation[] {
  const framesBySym = new Map<string, Frame[]>();
  for (const frame of options.frames) {
    const existing = framesBySym.get(frame.sym);
    if (existing) {
      existing.push(frame);
    } else {
      framesBySym.set(frame.sym, [frame]);
    }
  }
  for (const frames of framesBySym.values()) {
    frames.sort(compareFrames);
  }

  const frameIndices = new Map<string, number>();
  const symbolMetrics = new Map<string, SymbolMetrics>();
  const sortedOrders = [...options.orders].sort(compareOrders);
  for (const order of sortedOrders) {
    const metrics = ensureMetrics(symbolMetrics, order.sym);
    const qtyMinor = toMinor(order.quantity);
    const signedQty = order.side === 'buy' ? qtyMinor : -qtyMinor;
    const frame = findFrameForOrder(order, framesBySym, frameIndices);
    const priceSource = order.price ?? inferPriceFromFrame(order, frame);
    if (priceSource === undefined) {
      throw new Error(`Unable to determine price for order ${order.id}`);
    }
    const priceMinor = toMinor(priceSource);
    const absQtyMinor = qtyMinor < 0n ? -qtyMinor : qtyMinor;
    metrics.grossNotionalMinor += absQtyMinor * priceMinor;
    metrics.netQuantityMinor += signedQty;
    const exposurePriceMinor = frame ? toMinor(frame.last) : priceMinor;
    const netAbs = metrics.netQuantityMinor < 0n ? -metrics.netQuantityMinor : metrics.netQuantityMinor;
    const exposureMinor = netAbs * exposurePriceMinor;
    if (exposureMinor > metrics.maxAbsExposureMinor) {
      metrics.maxAbsExposureMinor = exposureMinor;
    }
    metrics.orderCount += 1;
  }

  const evaluations: RiskEvaluation[] = [];
  for (const [sym, metrics] of symbolMetrics) {
    evaluations.push({
      sym,
      orderCount: metrics.orderCount,
      grossNotional: formatMinor(metrics.grossNotionalMinor, DOUBLE_SCALE),
      netQuantity: formatMinor(metrics.netQuantityMinor, SCALE),
      maxAbsExposure: formatMinor(metrics.maxAbsExposureMinor, DOUBLE_SCALE),
    });
  }
  evaluations.sort((a, b) => (a.sym < b.sym ? -1 : a.sym > b.sym ? 1 : 0));
  return evaluations;
}

export function readOrdersNdjson(path: string): Order[] {
  const content = readFileSync(path, 'utf-8');
  return parseNdjson(content, assertValidOrder);
}

export function readFramesNdjson(path: string): Frame[] {
  const content = readFileSync(path, 'utf-8');
  return parseNdjson(content, assertValidFrame);
}

export function evaluateRiskFromPaths(options: EvaluateFromPathsOptions): RiskEvaluation[] {
  return evaluateRisk({
    orders: readOrdersNdjson(options.ordersPath),
    frames: readFramesNdjson(options.framesPath),
  });
}

export function writeEvaluationsNdjson(path: string, evaluations: RiskEvaluation[]): void {
  const directory = dirname(path);
  mkdirSync(directory, { recursive: true });
  const payload = evaluations.map((item) => JSON.stringify(item)).join('\n');
  writeFileSync(path, payload + (evaluations.length ? '\n' : ''));
}

function parseNdjson<T>(content: string, validator: (value: unknown) => T): T[] {
  return content
    .split(/\n/)
    .map((line) => line.trim())
    .filter((line) => line.length > 0)
    .map((line) => validator(JSON.parse(line)));
}

interface SymbolMetrics {
  orderCount: number;
  grossNotionalMinor: bigint;
  netQuantityMinor: bigint;
  maxAbsExposureMinor: bigint;
}

const SCALE = 8;
const DOUBLE_SCALE = SCALE * 2;
const SCALE_FACTOR = BigInt(10) ** BigInt(SCALE);
const DOUBLE_SCALE_FACTOR = BigInt(10) ** BigInt(DOUBLE_SCALE);

function ensureMetrics(map: Map<string, SymbolMetrics>, sym: string): SymbolMetrics {
  let metrics = map.get(sym);
  if (!metrics) {
    metrics = {
      orderCount: 0,
      grossNotionalMinor: 0n,
      netQuantityMinor: 0n,
      maxAbsExposureMinor: 0n,
    };
    map.set(sym, metrics);
  }
  return metrics;
}

function toMinor(value: number | string): bigint {
  return BigInt(toMinorUnits(value, SCALE));
}

function formatMinor(value: bigint, scale: number): string {
  if (scale === SCALE) {
    return canonNumber(formatMinorInternal(value, SCALE_FACTOR, scale));
  }
  if (scale === DOUBLE_SCALE) {
    return canonNumber(formatMinorInternal(value, DOUBLE_SCALE_FACTOR, scale));
  }
  const scaleFactor = BigInt(10) ** BigInt(scale);
  return canonNumber(formatMinorInternal(value, scaleFactor, scale));
}

function formatMinorInternal(value: bigint, scaleFactor: bigint, scale: number): string {
  const negative = value < 0n;
  let abs = negative ? -value : value;
  const intPart = abs / scaleFactor;
  const fracPart = abs % scaleFactor;
  let result = intPart.toString();
  if (scale > 0) {
    const width = scale;
    const frac = fracPart.toString().padStart(width, '0').replace(/0+$/, '');
    if (frac.length > 0) {
      result += `.${frac}`;
    }
  }
  if (negative && result !== '0') {
    result = `-${result}`;
  }
  return result;
}

function compareFrames(a: Frame, b: Frame): number {
  if (a.ts !== b.ts) {
    return a.ts - b.ts;
  }
  if (a.sym < b.sym) {
    return -1;
  }
  if (a.sym > b.sym) {
    return 1;
  }
  return a.seq - b.seq;
}

function compareOrders(a: Order, b: Order): number {
  if (a.ts !== b.ts) {
    return a.ts - b.ts;
  }
  if (a.sym < b.sym) {
    return -1;
  }
  if (a.sym > b.sym) {
    return 1;
  }
  return a.id.localeCompare(b.id);
}

function findFrameForOrder(
  order: Order,
  framesBySym: Map<string, Frame[]>,
  frameIndices: Map<string, number>,
): Frame | undefined {
  const frames = framesBySym.get(order.sym);
  if (!frames || frames.length === 0) {
    return undefined;
  }
  let index = frameIndices.get(order.sym) ?? 0;
  while (index + 1 < frames.length && frames[index + 1].ts <= order.ts) {
    index += 1;
  }
  frameIndices.set(order.sym, index);
  return frames[index];
}

function inferPriceFromFrame(order: Order, frame?: Frame): string | undefined {
  if (!frame) {
    return undefined;
  }
  if (order.side === 'buy') {
    return frame.ask ?? frame.last;
  }
  if (order.side === 'sell') {
    return frame.bid ?? frame.last;
  }
  return frame.last;
}

function main(argv: string[]): void {
  const [command, ...rest] = argv;
  if (command !== 'eval') {
    throw new Error(
      'Usage: pilot-risk eval --orders <orders.ndjson> --frames <frames.ndjson> --out <evaluations.ndjson>',
    );
  }
  const options = parseArgs(rest);
  const evaluations = evaluateRiskFromPaths({
    ordersPath: options.orders,
    framesPath: options.frames,
  });
  writeEvaluationsNdjson(options.out, evaluations);
}

interface CliOptions {
  orders: string;
  frames: string;
  out: string;
}

function parseArgs(args: string[]): CliOptions {
  const options: Partial<CliOptions> = {};
  for (let i = 0; i < args.length; i += 1) {
    const arg = args[i];
    switch (arg) {
      case '--orders':
        options.orders = resolve(args[++i]);
        break;
      case '--frames':
        options.frames = resolve(args[++i]);
        break;
      case '--out':
        options.out = resolve(args[++i]);
        break;
      default:
        throw new Error(`Unknown argument: ${arg}`);
    }
  }
  if (!options.orders || !options.frames || !options.out) {
    throw new Error('Missing required arguments');
  }
  return options as CliOptions;
}

const entrypoint = fileURLToPath(import.meta.url);
const invoked = process.argv[1] ? resolve(process.argv[1]) : undefined;

if (invoked && entrypoint === invoked) {
  main(process.argv.slice(2));
}

export { configSchema, validateConfig };
