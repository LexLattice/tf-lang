import Ajv, { ValidateFunction } from 'ajv';
import addFormats from 'ajv-formats';
import frameSchema from '../frame.schema.json';
import orderSchema from '../order.schema.json';
import stateSchema from '../state.schema.json';

export type DecimalString = string;

export interface Frame {
  ts: number;
  sym: string;
  seq: number;
  bid: DecimalString;
  ask: DecimalString;
  last: DecimalString;
  volume: DecimalString;
}

export interface Order {
  id: string;
  ts: number;
  sym: string;
  side: 'buy' | 'sell';
  type: 'market' | 'limit';
  price: DecimalString;
  qty: DecimalString;
  meta?: Record<string, string | number | boolean | null>;
}

export interface State {
  seed: number;
  positions: Record<string, DecimalString>;
  balances: Record<string, DecimalString>;
  meta?: Record<string, unknown>;
}

export type FrameInput = Omit<Frame, 'bid' | 'ask' | 'last' | 'volume'> & {
  bid: DecimalLike;
  ask: DecimalLike;
  last: DecimalLike;
  volume: DecimalLike;
};

export type DecimalLike = string | number | bigint;

const ajv = new Ajv({ allErrors: true, strict: false, useDefaults: false });
addFormats(ajv);

function compile<T>(schema: unknown): ValidateFunction<T> {
  return ajv.compile<T>(schema as any);
}

const validateFrameFn = compile<Frame>(frameSchema);
const validateOrderFn = compile<Order>(orderSchema);
const validateStateFn = compile<State>(stateSchema);

export function validateFrame(value: unknown): asserts value is Frame {
  if (!validateFrameFn(value)) {
    throw new Error(`Invalid frame: ${ajv.errorsText(validateFrameFn.errors)}`);
  }
}

export function validateOrder(value: unknown): asserts value is Order {
  if (!validateOrderFn(value)) {
    throw new Error(`Invalid order: ${ajv.errorsText(validateOrderFn.errors)}`);
  }
}

export function validateState(value: unknown): asserts value is State {
  if (!validateStateFn(value)) {
    throw new Error(`Invalid state: ${ajv.errorsText(validateStateFn.errors)}`);
  }
}

export function canonNumber(value: DecimalLike): DecimalString {
  let str: string;
  if (typeof value === 'string') {
    str = value.trim();
  } else if (typeof value === 'bigint') {
    str = value.toString();
  } else if (Number.isFinite(value)) {
    str = value.toString();
  } else {
    throw new Error(`Non-finite number: ${value}`);
  }

  if (!str) {
    return '0';
  }

  const negative = str.startsWith('-');
  if (negative || str.startsWith('+')) {
    str = str.slice(1);
  }

  if (!/^\d*(?:\.\d*)?$/.test(str)) {
    throw new Error(`Invalid decimal value: ${value}`);
  }

  let [intPart, fracPart = ''] = str.split('.');
  intPart = intPart.replace(/^0+(?=\d)/, '');
  fracPart = fracPart.replace(/0+$/, '');

  let normalized = intPart || '0';
  if (fracPart.length > 0) {
    normalized += `.${fracPart}`;
  }

  if (normalized === '0' && negative) {
    return '0';
  }

  return negative ? `-${normalized}` : normalized;
}

export function canonFrame(frame: FrameInput): Frame {
  const normalized: Frame = {
    ts: typeof frame.ts === 'string' ? Number.parseInt(frame.ts, 10) : frame.ts,
    sym: frame.sym,
    seq: typeof frame.seq === 'string' ? Number.parseInt(frame.seq, 10) : frame.seq,
    bid: canonNumber(frame.bid),
    ask: canonNumber(frame.ask),
    last: canonNumber(frame.last),
    volume: canonNumber(frame.volume)
  };

  validateFrame(normalized);
  return normalized;
}

export function toMinorUnits(value: DecimalLike, decimals: number): bigint {
  if (!Number.isInteger(decimals) || decimals < 0) {
    throw new Error(`Invalid decimals: ${decimals}`);
  }

  const canonical = canonNumber(value);
  const negative = canonical.startsWith('-');
  const digits = negative ? canonical.slice(1) : canonical;
  const [intPartRaw, fracPartRaw = ''] = digits.split('.');
  const intPart = intPartRaw || '0';
  if (fracPartRaw.length > decimals) {
    throw new Error(`Too many decimal places: ${canonical} for scale ${decimals}`);
  }
  const fracPart = (fracPartRaw + '0'.repeat(decimals)).slice(0, decimals);
  const scale = BigInt(10) ** BigInt(decimals);
  const base = BigInt(intPart);
  const fraction = fracPart ? BigInt(fracPart) : 0n;
  const total = base * scale + fraction;
  return negative ? -total : total;
}

export function seedRng(seed: number): () => number {
  let state = seed >>> 0;
  return () => {
    state = (state + 0x6d2b79f5) >>> 0;
    let t = state;
    t = Math.imul(t ^ (t >>> 15), t | 1);
    t ^= t + Math.imul(t ^ (t >>> 7), t | 61);
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  };
}

export const schemas = {
  frame: frameSchema,
  order: orderSchema,
  state: stateSchema
};
