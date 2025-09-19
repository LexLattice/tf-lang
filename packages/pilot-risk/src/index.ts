import { mkdirSync, readFileSync, writeFileSync } from 'node:fs';
import { dirname, resolve as resolvePath } from 'node:path';
import { fileURLToPath } from 'node:url';

import Ajv, { ValidateFunction } from 'ajv';

import {
  Frame,
  Order,
  assertValidFrame,
  assertValidOrder,
  canonNumber,
} from '@tf-lang/pilot-core';

import configSchema from './schemas/config.schema.json' with { type: 'json' };

export interface RiskConfig {
  mode: 'exposure';
  meta?: Record<string, unknown>;
}

export interface RiskEvaluationRecord {
  sym: string;
  firstTs: number | null;
  lastTs: number | null;
  frameCount: number;
  orderCount: number;
  grossNotional: string;
  netQuantity: string;
  maxAbsExposure: string;
}

export interface RiskContext {
  evaluate(frames: Frame[], orders: Order[]): RiskEvaluationRecord[];
}

const ajv = new Ajv({ allErrors: true, strict: false });
export const validateConfig: ValidateFunction<RiskConfig> = ajv.compile<RiskConfig>(configSchema as any);

export function createRisk(configInput: unknown): RiskContext {
  if (!validateConfig(configInput)) {
    throw new Error(ajv.errorsText(validateConfig.errors));
  }
  const config = configInput as RiskConfig;
  switch (config.mode) {
    case 'exposure':
      return { evaluate: evaluateExposure };
    default:
      throw new Error(`Unsupported risk mode: ${config.mode satisfies never}`);
  }
}

export function evaluateExposure(frames: Frame[], orders: Order[]): RiskEvaluationRecord[] {
  const framesBySym = groupBySymbol(frames, sortFrames);
  const ordersBySym = groupBySymbol(orders, sortOrders);
  const symbols = Array.from(new Set([...framesBySym.keys(), ...ordersBySym.keys()])).sort();
  const evaluations: RiskEvaluationRecord[] = [];
  for (const sym of symbols) {
    const symFrames = framesBySym.get(sym) ?? [];
    const symOrders = ordersBySym.get(sym) ?? [];
    evaluations.push(evaluateSymbolExposure(sym, symFrames, symOrders));
  }
  return evaluations;
}

export interface RiskRunOptions {
  framesPath: string;
  ordersPath: string;
  outPath: string;
  config?: unknown;
}

export function runRiskEvaluation(options: RiskRunOptions): RiskEvaluationRecord[] {
  const frames = readFramesNdjson(options.framesPath);
  const orders = readOrdersNdjson(options.ordersPath);
  const config = options.config ?? { mode: 'exposure' };
  const risk = createRisk(config);
  const evaluations = risk.evaluate(frames, orders);
  writeEvaluationsNdjson(options.outPath, evaluations);
  return evaluations;
}

export function readFramesNdjson(path: string): Frame[] {
  const content = readFileSync(path, 'utf-8');
  return parseNdjson(content).map((value) => assertValidFrame(value));
}

export function readOrdersNdjson(path: string): Order[] {
  const content = readFileSync(path, 'utf-8');
  return parseNdjson(content).map((value) => assertValidOrder(value));
}

export function writeEvaluationsNdjson(path: string, evaluations: RiskEvaluationRecord[]): void {
  const directory = dirname(path);
  mkdirSync(directory, { recursive: true });
  const content = evaluations.map((evaluation) => JSON.stringify(evaluation)).join('\n');
  writeFileSync(path, content + (evaluations.length ? '\n' : ''));
}

function parseNdjson(content: string): unknown[] {
  return content
    .split(/\r?\n/)
    .map((line) => line.trim())
    .filter((line) => line.length > 0)
    .map((line) => JSON.parse(line));
}

function evaluateSymbolExposure(sym: string, frames: Frame[], orders: Order[]): RiskEvaluationRecord {
  let netQuantity = 0;
  let grossNotional = 0;
  let maxAbsExposure = 0;
  let processedOrders = 0;
  let lastPrice = 0;
  let firstTs: number | null = null;
  let lastTs: number | null = null;
  let orderIndex = 0;

  const sortedOrders = orders;

  for (const frame of frames) {
    const framePrice = Number(frame.last);
    lastPrice = framePrice;
    if (firstTs === null) {
      firstTs = frame.ts;
    }
    lastTs = frame.ts;
    while (orderIndex < sortedOrders.length && sortedOrders[orderIndex].ts <= frame.ts) {
      const order = sortedOrders[orderIndex++];
      netQuantity = applyOrder(netQuantity, order);
      const executionPrice = order.price !== undefined ? Number(order.price) : framePrice;
      grossNotional += Math.abs(executionPrice * signedQuantity(order));
      processedOrders += 1;
      if (firstTs === null) {
        firstTs = order.ts;
      }
      lastTs = order.ts;
      if (order.price !== undefined) {
        lastPrice = Number(order.price);
      }
    }
    const exposure = Math.abs(netQuantity * framePrice);
    if (exposure > maxAbsExposure) {
      maxAbsExposure = exposure;
    }
  }

  while (orderIndex < sortedOrders.length) {
    const order = sortedOrders[orderIndex++];
    netQuantity = applyOrder(netQuantity, order);
    const executionPrice = order.price !== undefined ? Number(order.price) : lastPrice;
    grossNotional += Math.abs(executionPrice * signedQuantity(order));
    processedOrders += 1;
    if (order.price !== undefined) {
      lastPrice = Number(order.price);
    }
    if (firstTs === null) {
      firstTs = order.ts;
    }
    lastTs = order.ts;
    const exposure = Math.abs(netQuantity * (order.price !== undefined ? Number(order.price) : lastPrice));
    if (exposure > maxAbsExposure) {
      maxAbsExposure = exposure;
    }
  }

  const normalisedNet = Math.abs(netQuantity) === 0 ? 0 : netQuantity;
  return {
    sym,
    firstTs,
    lastTs,
    frameCount: frames.length,
    orderCount: processedOrders,
    grossNotional: canonNumber(grossNotional),
    netQuantity: canonNumber(normalisedNet),
    maxAbsExposure: canonNumber(maxAbsExposure),
  };
}

function applyOrder(current: number, order: Order): number {
  return current + signedQuantity(order);
}

function signedQuantity(order: Order): number {
  const qty = Number(order.quantity);
  return order.side === 'buy' ? qty : -qty;
}

function groupBySymbol<T extends Frame | Order>(
  values: T[],
  sorter: (collection: T[]) => T[],
): Map<string, T[]> {
  const grouped = new Map<string, T[]>();
  for (const value of values) {
    const list = grouped.get(value.sym);
    if (list) {
      list.push(value);
    } else {
      grouped.set(value.sym, [value]);
    }
  }
  for (const [sym, list] of grouped) {
    grouped.set(sym, sorter(list));
  }
  return grouped;
}

function sortFrames(frames: Frame[]): Frame[] {
  return [...frames].sort((a, b) => {
    if (a.ts !== b.ts) {
      return a.ts - b.ts;
    }
    return a.seq - b.seq;
  });
}

function sortOrders(orders: Order[]): Order[] {
  return [...orders].sort((a, b) => {
    if (a.ts !== b.ts) {
      return a.ts - b.ts;
    }
    if (a.id < b.id) {
      return -1;
    }
    if (a.id > b.id) {
      return 1;
    }
    return 0;
  });
}

function parseConfigFile(path: string): unknown {
  const content = readFileSync(path, 'utf-8');
  return JSON.parse(content);
}

interface CliOptions {
  frames: string;
  orders: string;
  out: string;
  config?: string;
}

function main(argv: string[]): void {
  if (argv.includes('--help')) {
    printHelp();
    return;
  }
  const [command, ...rest] = argv;
  if (command !== 'eval') {
    printHelp();
    throw new Error('Unknown command');
  }
  const options = parseArgs(rest);
  const config = options.config ? parseConfigFile(options.config) : { mode: 'exposure' };
  runRiskEvaluation({
    framesPath: options.frames,
    ordersPath: options.orders,
    outPath: options.out,
    config,
  });
}

function parseArgs(args: string[]): CliOptions {
  const options: Partial<CliOptions> = {};
  for (let i = 0; i < args.length; i += 1) {
    const arg = args[i];
    switch (arg) {
      case '--frames':
        options.frames = args[++i];
        break;
      case '--orders':
        options.orders = args[++i];
        break;
      case '--out':
        options.out = args[++i];
        break;
      case '--config':
        options.config = args[++i];
        break;
      case '--help':
        printHelp();
        return process.exit(0) as never;
      default:
        throw new Error(`Unknown argument: ${arg}`);
    }
  }
  if (!options.frames || !options.orders || !options.out) {
    printHelp();
    throw new Error('Missing required arguments');
  }
  return options as CliOptions;
}

function printHelp(): void {
  const lines = [
    'Usage: pilot-risk eval --frames <frames.ndjson> --orders <orders.ndjson> --out <evaluations.ndjson> [--config <file>]',
    '',
    'The default configuration runs exposure metrics with canonical outputs.',
  ];
  console.log(lines.join('\n'));
}

const entrypoint = fileURLToPath(import.meta.url);
const executed = process.argv[1] ? resolvePath(process.argv[1]) : '';
if (entrypoint === executed) {
  main(process.argv.slice(2));
}

export { configSchema };
