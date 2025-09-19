import Ajv, { ValidateFunction } from 'ajv';
import frameSchema from './schemas/frame.schema.json' with { type: 'json' };
import orderSchema from './schemas/order.schema.json' with { type: 'json' };
import stateSchema from './schemas/state.schema.json' with { type: 'json' };

export interface Frame {
  ts: number;
  sym: string;
  seq: number;
  bid: string;
  ask: string;
  last: string;
  volume: string;
  meta?: Record<string, unknown>;
}

export interface Order {
  id: string;
  ts: number;
  sym: string;
  side: 'buy' | 'sell';
  quantity: string;
  price?: string;
  meta?: Record<string, unknown>;
}

export interface State {
  seed: number;
  cash: string;
  positions: Record<string, string>;
  meta?: Record<string, unknown>;
}

export type FrameLike = Omit<Frame, 'bid' | 'ask' | 'last' | 'volume'> & {
  bid: number | string;
  ask: number | string;
  last: number | string;
  volume: number | string;
};

export type OrderLike = Omit<Order, 'quantity' | 'price'> & {
  quantity: number | string;
  price?: number | string;
};

const ajv = new Ajv({ allErrors: true, strict: false });

export const validateFrame: ValidateFunction<Frame> = ajv.compile<Frame>(frameSchema as any);
export const validateOrder: ValidateFunction<Order> = ajv.compile<Order>(orderSchema as any);
export const validateState: ValidateFunction<State> = ajv.compile<State>(stateSchema as any);

export function assertValidFrame(value: unknown): Frame {
  if (!validateFrame(value)) {
    throw new Error(ajv.errorsText(validateFrame.errors));
  }
  return value as Frame;
}

export function assertValidOrder(value: unknown): Order {
  if (!validateOrder(value)) {
    throw new Error(ajv.errorsText(validateOrder.errors));
  }
  return value as Order;
}

export function assertValidState(value: unknown): State {
  if (!validateState(value)) {
    throw new Error(ajv.errorsText(validateState.errors));
  }
  return value as State;
}

export function seedRng(seedInput: number | string): () => number {
  let seed = typeof seedInput === 'number' ? seedInput : hashString(seedInput);
  if (!Number.isFinite(seed)) {
    throw new Error('Seed must be finite');
  }
  let state = (seed >>> 0) + 0x6d2b79f5;
  return () => {
    state |= 0;
    state = (state + 0x6d2b79f5) | 0;
    let t = Math.imul(state ^ (state >>> 15), 1 | state);
    t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t;
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  };
}

function hashString(value: string): number {
  let hash = 0;
  for (let i = 0; i < value.length; i += 1) {
    hash = Math.imul(31, hash) + value.charCodeAt(i);
  }
  return hash;
}

export function canonNumber(value: number | string | bigint): string {
  if (typeof value === 'bigint') {
    return value.toString();
  }
  if (typeof value === 'number') {
    if (!Number.isFinite(value)) {
      throw new Error('Non-finite number');
    }
    return normaliseDecimal(value.toString());
  }
  const trimmed = value.trim();
  if (trimmed.length === 0) {
    throw new Error('Empty numeric string');
  }
  return normaliseDecimal(trimmed);
}

function normaliseDecimal(input: string): string {
  if (/^[-+]?\d+(\.\d+)?$/.test(input)) {
    return stripLeadingZeros(input);
  }
  const n = Number(input);
  if (!Number.isFinite(n)) {
    throw new Error(`Invalid numeric input: ${input}`);
  }
  return stripLeadingZeros(n.toString());
}

function stripLeadingZeros(input: string): string {
  let sign = '';
  let str = input;
  if (str.startsWith('+')) {
    str = str.slice(1);
  }
  if (str.startsWith('-')) {
    sign = '-';
    str = str.slice(1);
  }
  if (!str.includes('.')) {
    str = str.replace(/^0+(\d)/, '$1');
    return sign + (str.length === 0 ? '0' : str);
  }
  let [intPart, fracPart] = str.split('.', 2);
  intPart = intPart.replace(/^0+(\d)/, '$1');
  fracPart = fracPart.replace(/0+$/, '');
  if (intPart === '') {
    intPart = '0';
  }
  if (fracPart.length === 0) {
    return sign + intPart;
  }
  return sign + intPart + '.' + fracPart;
}

export function canonFrame(frame: FrameLike): Frame {
  const canonical: Frame = {
    ts: Number(frame.ts),
    sym: frame.sym,
    seq: Number(frame.seq),
    bid: canonNumber(frame.bid),
    ask: canonNumber(frame.ask),
    last: canonNumber(frame.last),
    volume: canonNumber(frame.volume),
    meta: frame.meta,
  };
  return assertValidFrame(canonical);
}

export function canonOrder(order: OrderLike): Order {
  const canonical: Order = {
    id: order.id,
    ts: Number(order.ts),
    sym: order.sym,
    side: order.side,
    quantity: canonNumber(order.quantity),
    price: order.price !== undefined ? canonNumber(order.price) : undefined,
    meta: order.meta,
  };
  return assertValidOrder(canonical);
}

export function toMinorUnits(value: number | string, scale: number): string {
  if (!Number.isInteger(scale) || scale < 0) {
    throw new Error('Scale must be a non-negative integer');
  }
  let canonical = canonNumber(value);
  const negative = canonical.startsWith('-');
  if (negative) {
    canonical = canonical.slice(1);
  }
  const [intPartRaw, fracPartRaw = ''] = canonical.split('.', 2);
  const intPart = intPartRaw === '' ? '0' : intPartRaw;
  let fracPart = fracPartRaw.padEnd(scale, '0');
  if (fracPart.length > scale) {
    throw new Error('Value has more precision than scale allows');
  }
  let digits = intPart + fracPart.slice(0, scale);
  digits = digits.replace(/^0+(\d)/, '$1');
  if (digits.length === 0) {
    digits = '0';
  }
  return negative && digits !== '0' ? '-' + digits : digits;
}

export { frameSchema, orderSchema, stateSchema };
