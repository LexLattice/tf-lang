import { readFileSync, writeFileSync } from 'node:fs';
import { dirname, resolve as resolvePath } from 'node:path';
import { mkdirSync } from 'node:fs';
import { fileURLToPath } from 'node:url';

import Ajv, { ValidateFunction } from 'ajv';
import { Frame, Order, canonNumber } from '@tf-lang/pilot-core';
import configSchema from './schemas/config.schema.json' with { type: 'json' };

export interface RiskConfig {
  mode: 'exposure';
  meta?: Record<string, unknown>;
}

export interface RiskEvaluation {
  sym: string;
  window: { startTs: number; endTs: number };
  metrics: {
    grossNotional: string;
    netQuantity: string;
    maxAbsExposure: string;
    orderCount: number;
  };
}

export interface EvaluateExposureOptions {
  orders: Order[];
  frames: Frame[];
}

export interface RiskCliOptions {
  orders: string;
  frames: string;
  out: string;
}

const ajv = new Ajv({ allErrors: true, strict: false });
export const validateConfig: ValidateFunction<RiskConfig> = ajv.compile<RiskConfig>(configSchema as any);

export function parseRiskConfig(config: unknown): RiskConfig {
  if (!validateConfig(config)) {
    throw new Error(ajv.errorsText(validateConfig.errors));
  }
  return config as RiskConfig;
}

interface DecimalValue {
  int: bigint;
  scale: number;
}

function decimalZero(): DecimalValue {
  return { int: 0n, scale: 0 };
}

function pow10(exp: number): bigint {
  return 10n ** BigInt(exp);
}

function normalizeDecimal(value: DecimalValue): DecimalValue {
  if (value.int === 0n) {
    return { int: 0n, scale: 0 };
  }
  let int = value.int;
  let scale = value.scale;
  while (scale > 0 && int % 10n === 0n) {
    int /= 10n;
    scale -= 1;
  }
  return { int, scale };
}

function parseDecimal(raw: string): DecimalValue {
  const canonical = canonNumber(raw);
  const negative = canonical.startsWith('-');
  const unsigned = negative ? canonical.slice(1) : canonical;
  const [intPartRaw, fracPartRaw = ''] = unsigned.split('.', 2);
  const digits = `${intPartRaw === '0' ? '' : intPartRaw}${fracPartRaw}`;
  const coeffStr = digits.length === 0 ? '0' : digits;
  const coeff = BigInt((negative ? '-' : '') + coeffStr);
  return normalizeDecimal({ int: coeff, scale: fracPartRaw.length });
}

function alignScale(value: DecimalValue, scale: number): bigint {
  if (value.scale === scale) {
    return value.int;
  }
  if (value.scale > scale) {
    throw new Error('Cannot align decimal to smaller scale');
  }
  const factor = pow10(scale - value.scale);
  return value.int * factor;
}

function decimalAdd(a: DecimalValue, b: DecimalValue): DecimalValue {
  const scale = Math.max(a.scale, b.scale);
  const aInt = alignScale(a, scale);
  const bInt = alignScale(b, scale);
  return normalizeDecimal({ int: aInt + bInt, scale });
}

function decimalNegate(value: DecimalValue): DecimalValue {
  return { int: -value.int, scale: value.scale };
}

function decimalAbs(value: DecimalValue): DecimalValue {
  return value.int < 0n ? decimalNegate(value) : value;
}

function decimalMultiply(a: DecimalValue, b: DecimalValue): DecimalValue {
  return normalizeDecimal({ int: a.int * b.int, scale: a.scale + b.scale });
}

function decimalCompare(a: DecimalValue, b: DecimalValue): number {
  const scale = Math.max(a.scale, b.scale);
  const aInt = alignScale(a, scale);
  const bInt = alignScale(b, scale);
  if (aInt === bInt) {
    return 0;
  }
  return aInt > bInt ? 1 : -1;
}

function decimalToString(value: DecimalValue): string {
  const normalized = normalizeDecimal(value);
  const negative = normalized.int < 0n;
  const absInt = negative ? -normalized.int : normalized.int;
  const digits = absInt.toString();
  if (normalized.scale === 0) {
    return negative ? `-${digits}` : digits;
  }
  const scale = normalized.scale;
  const padded = digits.padStart(scale + 1, '0');
  const whole = padded.slice(0, padded.length - scale) || '0';
  const fraction = padded.slice(padded.length - scale);
  const trimmedWhole = whole.replace(/^0+(?=\d)/, '');
  const frac = fraction.replace(/0+$/, '');
  if (frac.length === 0) {
    return negative ? `-${trimmedWhole || '0'}` : trimmedWhole || '0';
  }
  return (negative ? '-' : '') + (trimmedWhole || '0') + '.' + frac;
}

interface SymbolAccumulator {
  startTs: number;
  endTs: number;
  netQty: DecimalValue;
  grossNotional: DecimalValue;
  maxAbsExposure: DecimalValue;
  orderCount: number;
  frames: Frame[];
  frameCursor: number;
  lastFrame?: Frame;
}

function createAccumulator(): SymbolAccumulator {
  return {
    startTs: Number.POSITIVE_INFINITY,
    endTs: Number.NEGATIVE_INFINITY,
    netQty: decimalZero(),
    grossNotional: decimalZero(),
    maxAbsExposure: decimalZero(),
    orderCount: 0,
    frames: [],
    frameCursor: 0,
  };
}

function ensureAccumulator(map: Map<string, SymbolAccumulator>, sym: string): SymbolAccumulator {
  let acc = map.get(sym);
  if (!acc) {
    acc = createAccumulator();
    map.set(sym, acc);
  }
  return acc;
}

export function evaluateExposure(options: EvaluateExposureOptions): RiskEvaluation[] {
  const accumulators = new Map<string, SymbolAccumulator>();
  const sortedFrames = [...options.frames].sort((a, b) => (a.ts - b.ts) || (a.seq - b.seq));
  for (const frame of sortedFrames) {
    const acc = ensureAccumulator(accumulators, frame.sym);
    acc.frames.push(frame);
    acc.startTs = Math.min(acc.startTs, frame.ts);
    acc.endTs = Math.max(acc.endTs, frame.ts);
  }

  const sortedOrders = [...options.orders].sort((a, b) => {
    if (a.ts !== b.ts) {
      return a.ts - b.ts;
    }
    if (a.sym !== b.sym) {
      return a.sym.localeCompare(b.sym);
    }
    return a.id.localeCompare(b.id);
  });

  for (const order of sortedOrders) {
    const acc = ensureAccumulator(accumulators, order.sym);
    acc.startTs = Math.min(acc.startTs, order.ts);
    acc.endTs = Math.max(acc.endTs, order.ts);
    const frames = acc.frames;
    while (acc.frameCursor < frames.length && frames[acc.frameCursor].ts <= order.ts) {
      acc.lastFrame = frames[acc.frameCursor];
      acc.frameCursor += 1;
    }
    const referenceFrame = acc.lastFrame ?? frames[0];
    const priceSource = order.price ?? referenceFrame?.last ?? referenceFrame?.ask ?? referenceFrame?.bid;
    if (!priceSource) {
      throw new Error(`Unable to determine price for order ${order.id}`);
    }
    const qty = parseDecimal(order.quantity);
    const signedQty = order.side === 'buy' ? qty : decimalNegate(qty);
    acc.netQty = decimalAdd(acc.netQty, signedQty);
    const absQty = decimalAbs(qty);
    const price = parseDecimal(priceSource);
    const notional = decimalMultiply(absQty, price);
    acc.grossNotional = decimalAdd(acc.grossNotional, notional);
    const exposure = decimalAbs(decimalMultiply(acc.netQty, price));
    if (decimalCompare(exposure, acc.maxAbsExposure) > 0) {
      acc.maxAbsExposure = exposure;
    }
    acc.orderCount += 1;
  }

  const evaluations: RiskEvaluation[] = [];
  for (const [sym, acc] of [...accumulators.entries()].sort(([a], [b]) => a.localeCompare(b))) {
    if (acc.startTs === Number.POSITIVE_INFINITY) {
      continue;
    }
    evaluations.push({
      sym,
      window: { startTs: acc.startTs, endTs: acc.endTs },
      metrics: {
        grossNotional: decimalToString(acc.grossNotional),
        netQuantity: decimalToString(acc.netQty),
        maxAbsExposure: decimalToString(acc.maxAbsExposure),
        orderCount: acc.orderCount,
      },
    });
  }
  return evaluations;
}

export function readOrdersNdjson(path: string): Order[] {
  const content = readFileSync(path, 'utf-8');
  return content
    .split(/\n/)
    .filter((line) => line.trim().length > 0)
    .map((line) => JSON.parse(line) as Order);
}

export function readFramesNdjson(path: string): Frame[] {
  const content = readFileSync(path, 'utf-8');
  return content
    .split(/\n/)
    .filter((line) => line.trim().length > 0)
    .map((line) => JSON.parse(line) as Frame);
}

export function writeEvaluationsNdjson(path: string, evaluations: RiskEvaluation[]): void {
  const directory = dirname(path);
  mkdirSync(directory, { recursive: true });
  const content = evaluations.map((entry) => JSON.stringify(entry)).join('\n');
  writeFileSync(path, content + (evaluations.length ? '\n' : ''));
}

function main(argv: string[]): void {
  const [command, ...rest] = argv;
  if (!command || command === '--help' || command === 'help') {
    printUsage();
    return;
  }
  if (command !== 'eval') {
    printUsage(true);
    return;
  }
  const options = parseCliArgs(rest);
  const orders = readOrdersNdjson(options.orders);
  const frames = readFramesNdjson(options.frames);
  const evaluations = evaluateExposure({ orders, frames });
  writeEvaluationsNdjson(options.out, evaluations);
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
        printUsage();
        process.exit(0);
      default:
        throw new Error(`Unknown argument: ${arg}`);
    }
  }
  if (!options.orders || !options.frames || !options.out) {
    throw new Error('Missing required arguments');
  }
  return options as RiskCliOptions;
}

function printUsage(error = false): void {
  const lines = [
    'Usage: pilot-risk eval --orders <file> --frames <file> --out <file>',
    '',
    'Computes exposure metrics per symbol using deterministic decimal arithmetic.',
  ];
  const stream = error ? process.stderr : process.stdout;
  stream.write(lines.join('\n') + '\n');
}

const entryPath = fileURLToPath(import.meta.url);
const invokedPath = process.argv[1] ? resolvePath(process.argv[1]) : '';

if (entryPath === invokedPath) {
  main(process.argv.slice(2));
}

export { configSchema };
