import Ajv, { ValidateFunction } from 'ajv';
import { mkdirSync, readFileSync, writeFileSync } from 'node:fs';
import { dirname, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';

import { Frame, Order, canonNumber } from '@tf-lang/pilot-core';
import configSchema from './schemas/config.schema.json' with { type: 'json' };

export interface RiskConfig {
  mode: 'passThrough' | 'exposure';
  meta?: Record<string, unknown>;
}

export interface RiskMetrics {
  sym: string;
  grossNotional: string;
  netQty: string;
  maxAbsExposure: string;
  orders: number;
}

export interface RiskEvaluationResult {
  orders: Order[];
  metrics: RiskMetrics[];
}

export interface RiskContext {
  evaluate(orders: Order[], frames: Frame[]): RiskEvaluationResult;
}

const ajv = new Ajv({ allErrors: true, strict: false });
const validateConfig: ValidateFunction<RiskConfig> = ajv.compile<RiskConfig>(configSchema as any);

export function createRisk(config: unknown): RiskContext {
  if (!validateConfig(config)) {
    throw new Error(ajv.errorsText(validateConfig.errors));
  }
  const parsed = config as RiskConfig;
  if (parsed.mode === 'passThrough') {
    return {
      evaluate(orders: Order[], _frames: Frame[]): RiskEvaluationResult {
        return { orders, metrics: [] };
      },
    };
  }
  return {
    evaluate(orders: Order[], frames: Frame[]): RiskEvaluationResult {
      const metrics = evaluateExposureMetrics(orders, frames);
      return { orders, metrics };
    },
  };
}

export function readOrdersNdjson(path: string): Order[] {
  const content = readFileSync(path, 'utf-8');
  return content
    .split(/\r?\n/)
    .filter((line) => line.trim().length > 0)
    .map((line) => JSON.parse(line) as Order);
}

export function readFramesNdjson(path: string): Frame[] {
  const content = readFileSync(path, 'utf-8');
  return content
    .split(/\r?\n/)
    .filter((line) => line.trim().length > 0)
    .map((line) => JSON.parse(line) as Frame);
}

export function writeEvaluationsNdjson(path: string, metrics: RiskMetrics[]): void {
  const directory = dirname(path);
  mkdirSync(directory, { recursive: true });
  const content = metrics.map((metric) => JSON.stringify(metric)).join('\n');
  writeFileSync(path, content + (metrics.length ? '\n' : ''));
}

export function evaluateExposureMetrics(orders: Order[], frames: Frame[]): RiskMetrics[] {
  const sortedOrders = [...orders].sort((a, b) => {
    if (a.ts !== b.ts) {
      return a.ts - b.ts;
    }
    if (a.sym !== b.sym) {
      return a.sym < b.sym ? -1 : 1;
    }
    return a.id < b.id ? -1 : a.id > b.id ? 1 : 0;
  });
  const frameLookup = buildFrameLookup(frames);
  const accumulators = new Map<string, SymbolAccumulator>();
  for (const order of sortedOrders) {
    const accumulator = getAccumulator(accumulators, order.sym);
    const priceDecimal = order.price
      ? parseDecimal(order.price)
      : lookupFramePrice(order, frameLookup);
    const qtyDecimal = parseDecimal(order.quantity);
    const signedQty = order.side === 'buy' ? qtyDecimal : negateDecimal(qtyDecimal);
    const absQty = absDecimal(signedQty);
    const notional = multiplyDecimal(absQty, priceDecimal);
    accumulator.grossNotional = addDecimal(accumulator.grossNotional, notional);
    accumulator.runningNetQty = addDecimal(accumulator.runningNetQty, signedQty);
    accumulator.netQty = accumulator.runningNetQty;
    const exposure = multiplyDecimal(absDecimal(accumulator.runningNetQty), priceDecimal);
    accumulator.maxAbsExposure = maxDecimal(accumulator.maxAbsExposure, exposure);
    accumulator.orders += 1;
  }
  const results: RiskMetrics[] = [];
  for (const [sym, accumulator] of [...accumulators.entries()].sort(([a], [b]) => (a < b ? -1 : a > b ? 1 : 0))) {
    results.push({
      sym,
      grossNotional: decimalToString(accumulator.grossNotional),
      netQty: decimalToString(accumulator.netQty),
      maxAbsExposure: decimalToString(accumulator.maxAbsExposure),
      orders: accumulator.orders,
    });
  }
  return results;
}

interface SymbolAccumulator {
  grossNotional: DecimalValue;
  netQty: DecimalValue;
  maxAbsExposure: DecimalValue;
  runningNetQty: DecimalValue;
  orders: number;
}

interface DecimalValue {
  value: bigint;
  scale: number;
}

function getAccumulator(map: Map<string, SymbolAccumulator>, sym: string): SymbolAccumulator {
  let accumulator = map.get(sym);
  if (!accumulator) {
    accumulator = {
      grossNotional: zeroDecimal(),
      netQty: zeroDecimal(),
      maxAbsExposure: zeroDecimal(),
      runningNetQty: zeroDecimal(),
      orders: 0,
    };
    map.set(sym, accumulator);
  }
  return accumulator;
}

function zeroDecimal(): DecimalValue {
  return { value: 0n, scale: 0 };
}

function buildFrameLookup(frames: Frame[]): Map<string, Frame[]> {
  const map = new Map<string, Frame[]>();
  for (const frame of frames) {
    if (!map.has(frame.sym)) {
      map.set(frame.sym, []);
    }
    map.get(frame.sym)!.push(frame);
  }
  for (const framesForSym of map.values()) {
    framesForSym.sort((a, b) => a.ts - b.ts);
  }
  return map;
}

function lookupFramePrice(order: Order, frames: Map<string, Frame[]>): DecimalValue {
  const series = frames.get(order.sym) ?? [];
  let candidate: Frame | undefined;
  for (const frame of series) {
    if (frame.ts <= order.ts) {
      candidate = frame;
    } else {
      break;
    }
  }
  const fallback = candidate ?? series[series.length - 1];
  if (!fallback) {
    throw new Error(`Unable to locate frame price for order ${order.id}`);
  }
  return parseDecimal(fallback.last);
}

function parseDecimal(input: string): DecimalValue {
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

function addDecimal(a: DecimalValue, b: DecimalValue): DecimalValue {
  const scale = Math.max(a.scale, b.scale);
  const aScaled = alignScale(a, scale);
  const bScaled = alignScale(b, scale);
  return { value: aScaled.value + bScaled.value, scale };
}

function multiplyDecimal(a: DecimalValue, b: DecimalValue): DecimalValue {
  return { value: a.value * b.value, scale: a.scale + b.scale };
}

function absDecimal(value: DecimalValue): DecimalValue {
  return value.value < 0n ? { value: -value.value, scale: value.scale } : value;
}

function negateDecimal(value: DecimalValue): DecimalValue {
  return { value: -value.value, scale: value.scale };
}

function maxDecimal(a: DecimalValue, b: DecimalValue): DecimalValue {
  const scale = Math.max(a.scale, b.scale);
  const aScaled = alignScale(a, scale);
  const bScaled = alignScale(b, scale);
  return aScaled.value >= bScaled.value ? aScaled : bScaled;
}

function alignScale(value: DecimalValue, targetScale: number): DecimalValue {
  if (value.scale === targetScale) {
    return value;
  }
  const diff = targetScale - value.scale;
  if (diff < 0) {
    throw new Error('Cannot downscale decimal value without precision loss');
  }
  return { value: value.value * pow10(diff), scale: targetScale };
}

function pow10(exp: number): bigint {
  let result = 1n;
  for (let i = 0; i < exp; i += 1) {
    result *= 10n;
  }
  return result;
}

function decimalToString(value: DecimalValue): string {
  const negative = value.value < 0n;
  const absValue = negative ? -value.value : value.value;
  if (value.scale === 0) {
    return canonNumber(`${negative ? '-' : ''}${absValue.toString()}`);
  }
  const str = absValue.toString().padStart(value.scale + 1, '0');
  const intPart = str.slice(0, str.length - value.scale);
  const fracPart = str.slice(str.length - value.scale);
  const composed = `${negative ? '-' : ''}${intPart}.${fracPart}`;
  return canonNumber(composed);
}

function printHelp(): void {
  console.log('Usage: pilot-risk eval --orders <file> --frames <file> --out <file>');
}

function main(argv: string[]): void {
  const [command, ...rest] = argv;
  if (command !== 'eval') {
    printHelp();
    throw new Error('Expected eval command');
  }
  const options = parseCliArgs(rest);
  const orders = readOrdersNdjson(options.orders);
  const frames = readFramesNdjson(options.frames);
  const metrics = evaluateExposureMetrics(orders, frames);
  writeEvaluationsNdjson(options.out, metrics);
}

interface RiskCliOptions {
  orders: string;
  frames: string;
  out: string;
}

function parseCliArgs(args: string[]): RiskCliOptions {
  const options: Partial<RiskCliOptions> = {};
  for (let i = 0; i < args.length; i += 1) {
    const arg = args[i];
    switch (arg) {
      case '--orders':
        options.orders = args[++i];
        break;
      case '--frames':
        options.frames = args[++i];
        break;
      case '--out':
        options.out = args[++i];
        break;
      case '--help':
      case '-h':
        printHelp();
        process.exit(0);
        break;
      default:
        throw new Error(`Unknown argument: ${arg}`);
    }
  }
  if (!options.orders || !options.frames || !options.out) {
    throw new Error('Missing required arguments');
  }
  return options as RiskCliOptions;
}

const entryPath = fileURLToPath(import.meta.url);
if (process.argv[1] && entryPath === resolve(process.argv[1])) {
  main(process.argv.slice(2));
}

export { configSchema, validateConfig };
