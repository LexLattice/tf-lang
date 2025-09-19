import { z } from 'zod';
import { createRequire } from 'node:module';

const require = createRequire(import.meta.url);
const frameSchemaJson = require('./schemas/frame.schema.json');
const orderSchemaJson = require('./schemas/order.schema.json');
const stateSchemaJson = require('./schemas/state.schema.json');

const decimalRegex = /^[-+]?\d+(?:\.\d+)?$/;
const integerRegex = /^[-+]?\d+$/;

const numericString = z
  .string()
  .min(1)
  .regex(decimalRegex, 'Invalid decimal string');

const integerString = z
  .string()
  .min(1)
  .regex(integerRegex, 'Invalid integer string');

export const FrameSchema = z.object({
  ts: integerString,
  sym: z.string().min(1),
  seq: z.number().int().min(0),
  bid: numericString.optional(),
  ask: numericString.optional(),
  last: numericString.optional(),
  vol: numericString.optional(),
  meta: z.record(z.unknown()).optional()
});

export type Frame = z.infer<typeof FrameSchema>;

export const OrderSchema = z.object({
  id: z.string().min(1),
  ts: integerString,
  sym: z.string().min(1),
  side: z.enum(['buy', 'sell']),
  type: z.enum(['market', 'limit']),
  qty: numericString,
  price: numericString.optional(),
  meta: z.record(z.unknown()).optional()
});

export type Order = z.infer<typeof OrderSchema>;

const PositionSchema = z.object({
  qty: numericString,
  avgPrice: numericString.optional(),
  meta: z.record(z.unknown()).optional()
});

export const StateSchema = z.object({
  cash: numericString,
  positions: z.record(PositionSchema),
  context: z.record(z.unknown()).optional(),
  meta: z.record(z.unknown()).optional()
});

export type State = z.infer<typeof StateSchema>;

export const frameJsonSchema = frameSchemaJson;
export const orderJsonSchema = orderSchemaJson;
export const stateJsonSchema = stateSchemaJson;

export interface FrameInput {
  ts: string | number | bigint;
  sym: string;
  seq: number | bigint;
  bid?: string | number | bigint;
  ask?: string | number | bigint;
  last?: string | number | bigint;
  vol?: string | number | bigint;
  meta?: Record<string, unknown>;
}

function normalizeInteger(value: string | number | bigint): string {
  const str = canonNumber(value);
  if (!integerRegex.test(str)) {
    throw new Error(`Expected integer-compatible value, received ${value}`);
  }
  return str.replace(/^\+/, '');
}

export function canonNumber(value: string | number | bigint): string {
  if (typeof value === 'number') {
    if (!Number.isFinite(value)) {
      throw new Error('Cannot canonicalise non-finite numbers');
    }
    value = value.toString();
  }

  if (typeof value === 'bigint') {
    return value.toString();
  }

  const trimmed = value.trim();
  if (!decimalRegex.test(trimmed)) {
    throw new Error(`Invalid numeric value: ${value}`);
  }

  const sign = trimmed.startsWith('-') ? '-' : trimmed.startsWith('+') ? '+' : '';
  const unsigned = sign ? trimmed.slice(1) : trimmed;
  const [intPartRaw, fracPartRaw = ''] = unsigned.split('.');
  const intPart = intPartRaw.replace(/^0+(?=\d)/, '');
  const fracPart = fracPartRaw.replace(/0+$/, '');
  const normalInt = intPart === '' ? '0' : intPart;
  const body = fracPart.length > 0 ? `${normalInt}.${fracPart}` : normalInt;
  if (body === '0') {
    return '0';
  }
  return `${sign === '-' ? '-' : ''}${body}`;
}

export function toMinorUnits(value: string | number | bigint, scale: number) {
  if (!Number.isInteger(scale) || scale < 0) {
    throw new Error('Scale must be a non-negative integer');
  }
  const canonical = canonNumber(value);
  const negative = canonical.startsWith('-');
  const unsigned = negative ? canonical.slice(1) : canonical;
  const [intPart, fracPartRaw = ''] = unsigned.split('.');
  if (fracPartRaw.length > scale) {
    throw new Error('Value has more fractional precision than scale');
  }
  const fracPart = fracPartRaw.padEnd(scale, '0');
  const digits = `${intPart}${fracPart}`.replace(/^0+(?=\d)/, '');
  const units = digits === '' ? '0' : digits;
  const signedUnits = negative && units !== '0' ? `-${units}` : units;
  return { units: signedUnits, scale };
}

export function canonFrame(input: FrameInput): Frame {
  const seq = typeof input.seq === 'bigint' ? Number(input.seq) : Number(input.seq);
  if (!Number.isFinite(seq) || !Number.isInteger(seq) || seq < 0) {
    throw new Error('Sequence must be a non-negative integer');
  }

  const base: Record<string, unknown> = {
    ts: normalizeInteger(input.ts),
    sym: input.sym.trim(),
    seq
  };

  for (const key of ['bid', 'ask', 'last', 'vol'] as const) {
    const value = input[key];
    if (value !== undefined) {
      base[key] = canonNumber(value);
    }
  }

  if (input.meta) {
    base.meta = input.meta;
  }

  return FrameSchema.parse(base);
}

export type Rng = () => number;

export function seedRng(seed: number | string | bigint): Rng {
  let state = (() => {
    if (typeof seed === 'bigint') {
      return Number(seed & BigInt(0xffffffff));
    }
    if (typeof seed === 'number') {
      return seed >>> 0;
    }
    let hash = 0;
    for (let i = 0; i < seed.length; i += 1) {
      hash = Math.imul(31, hash) + seed.charCodeAt(i);
      hash |= 0;
    }
    return hash >>> 0;
  })();

  return () => {
    state = (state + 0x6d2b79f5) | 0;
    let t = Math.imul(state ^ (state >>> 15), 1 | state);
    t ^= t + Math.imul(t ^ (t >>> 7), 61 | t);
    const result = ((t ^ (t >>> 14)) >>> 0) / 4294967296;
    return result;
  };
}

export function createIdFactory(seed: number | string | bigint) {
  const rng = seedRng(seed);
  let counter = 0;
  return () => {
    counter += 1;
    const n = Math.floor(rng() * 1e9)
      .toString()
      .padStart(9, '0');
    return `${counter}-${n}`;
  };
}

export const validators = {
  frame: (value: unknown) => FrameSchema.parse(value),
  order: (value: unknown) => OrderSchema.parse(value),
  state: (value: unknown) => StateSchema.parse(value)
};

export type { FrameInput as CanonicalFrameInput };
