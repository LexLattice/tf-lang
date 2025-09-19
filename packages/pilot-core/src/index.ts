import { z } from "zod";

export type OrderSide = "buy" | "sell";
export type OrderType = "limit" | "market";

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
  ts: number;
  sym: string;
  id: string;
  side: OrderSide;
  type: OrderType;
  price: string;
  size: string;
  meta?: Record<string, unknown>;
}

export interface StrategyState {
  seed: number;
  positions: Record<string, string>;
  pnl?: string;
  meta?: Record<string, unknown>;
}

const numericInput = z.union([z.number(), z.string()]);

const frameInputSchema = z
  .object({
    ts: z.union([z.number(), z.string()]),
    sym: z.string(),
    seq: z.union([z.number(), z.string()]).optional().default(0),
    bid: numericInput,
    ask: numericInput,
    last: numericInput,
    volume: numericInput.optional().default("0"),
    meta: z.record(z.any()).optional(),
  })
  .strict();

const orderInputSchema = z
  .object({
    ts: z.union([z.number(), z.string()]),
    sym: z.string(),
    id: z.string(),
    side: z.enum(["buy", "sell"]),
    type: z.enum(["limit", "market"]),
    price: numericInput,
    size: numericInput,
    meta: z.record(z.any()).optional(),
  })
  .strict();

const stateInputSchema = z
  .object({
    seed: z.number(),
    positions: z.record(z.string()),
    pnl: z.string().optional(),
    meta: z.record(z.any()).optional(),
  })
  .strict();

export const frameSchema = frameInputSchema.transform((data: z.infer<typeof frameInputSchema>): Frame => {
  return canonFrame({
    ts: Number(data.ts),
    sym: data.sym,
    seq: Number(data.seq),
    bid: canonNumber(data.bid),
    ask: canonNumber(data.ask),
    last: canonNumber(data.last),
    volume: canonNumber(data.volume),
    meta: data.meta,
  });
});

export const orderSchema = orderInputSchema.transform((data: z.infer<typeof orderInputSchema>): Order => {
  return {
    ts: Number(data.ts),
    sym: data.sym,
    id: data.id,
    side: data.side,
    type: data.type,
    price: canonNumber(data.price),
    size: canonNumber(data.size),
    meta: data.meta,
  };
});

export const stateSchema = stateInputSchema;

export type CanonFrame = z.infer<typeof frameSchema>;
export type CanonOrder = z.infer<typeof orderSchema>;
export type CanonState = z.infer<typeof stateSchema>;

export interface SeedRng {
  (): number;
  int(max: number): number;
}

export function seedRng(seed: number): SeedRng {
  let x = seed | 0;
  if (x === 0) {
    x = 0x6d2b79f5;
  }
  const nextInt32 = () => {
    x |= 0;
    x ^= x << 13;
    x ^= x >>> 17;
    x ^= x << 5;
    return (x >>> 0) & 0xffffffff;
  };
  const rng = () => {
    const value = nextInt32();
    return (value + 1) / 4294967297;
  };
  rng.int = (max: number) => {
    if (!Number.isFinite(max) || max <= 0) {
      throw new Error("seedRng.int requires a positive max");
    }
    return Math.floor(rng() * max);
  };
  return rng as SeedRng;
}

export interface CanonNumberOptions {
  maxDecimals?: number;
}

export function canonNumber(value: number | string, options: CanonNumberOptions = {}): string {
  const maxDecimals = options.maxDecimals;
  if (typeof value === "number") {
    if (!Number.isFinite(value)) {
      throw new Error(`Invalid numeric value: ${value}`);
    }
    if (Number.isInteger(value)) {
      return value.toString();
    }
    const numeric = value.toString();
    if (numeric.includes("e") || numeric.includes("E")) {
      const decimals = maxDecimals ?? 12;
      return canonNumber(value.toFixed(decimals));
    }
    return canonNumber(numeric, options);
  }
  const raw = value.trim();
  if (raw === "") {
    throw new Error("Numeric string cannot be empty");
  }
  if (!/^[-+]?\d*(?:\.\d*)?$/.test(raw)) {
    throw new Error(`Invalid numeric string: ${value}`);
  }
  let sign = "";
  let body = raw;
  if (body.startsWith("-")) {
    sign = "-";
    body = body.slice(1);
  } else if (body.startsWith("+")) {
    body = body.slice(1);
  }
  if (body.includes("e") || body.includes("E")) {
    const decimals = maxDecimals ?? 12;
    const numeric = Number(`${sign}${body}`);
    if (!Number.isFinite(numeric)) {
      throw new Error(`Invalid numeric value: ${value}`);
    }
    return canonNumber(numeric.toFixed(decimals));
  }
  let [integerPart, fractionalPart = ""] = body.split(".");
  if (integerPart === "") {
    integerPart = "0";
  }
  if (!/^[0-9]+$/.test(integerPart) || !/^[0-9]*$/.test(fractionalPart)) {
    throw new Error(`Invalid numeric string: ${value}`);
  }
  integerPart = integerPart.replace(/^0+(?=\d)/, "");
  if (integerPart === "") {
    integerPart = "0";
  }
  if (maxDecimals !== undefined) {
    fractionalPart = fractionalPart.slice(0, maxDecimals);
  }
  fractionalPart = fractionalPart.replace(/0+$/, "");
  if (fractionalPart.length === 0) {
    return `${sign}${integerPart}`;
  }
  return `${sign}${integerPart}.${fractionalPart}`;
}

export function toMinorUnits(value: number | string, decimals: number): string {
  if (!Number.isInteger(decimals) || decimals < 0) {
    throw new Error("decimals must be a non-negative integer");
  }
  const canonical = canonNumber(value, { maxDecimals: decimals });
  const [integerPartRaw, fractionPartRaw = ""] = canonical.split(".");
  const isNegative = integerPartRaw.startsWith("-");
  const integerPart = isNegative ? integerPartRaw.slice(1) : integerPartRaw;
  const normalizedFraction = (fractionPartRaw + "0".repeat(decimals)).slice(0, decimals);
  const combined = `${integerPart}${normalizedFraction}`.replace(/^0+(\d)/, "$1");
  const unsigned = combined === "" ? "0" : combined;
  const prefixed = isNegative && unsigned !== "0" ? `-${unsigned}` : unsigned;
  return BigInt(prefixed).toString();
}

export function canonFrame(frame: Frame): Frame {
  return {
    ts: frame.ts,
    sym: frame.sym,
    seq: frame.seq,
    bid: canonNumber(frame.bid),
    ask: canonNumber(frame.ask),
    last: canonNumber(frame.last),
    volume: canonNumber(frame.volume),
    meta: frame.meta ? { ...frame.meta } : undefined,
  };
}

export function validateFrame(data: unknown): Frame {
  return frameSchema.parse(data);
}

export function validateOrder(data: unknown): Order {
  return orderSchema.parse(data);
}

export function validateState(data: unknown): StrategyState {
  return stateSchema.parse(data);
}
