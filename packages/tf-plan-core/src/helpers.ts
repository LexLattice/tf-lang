import { createHash } from "node:crypto";

export interface StableIdInput {
  readonly scope?: string;
  readonly specId: string;
  readonly component: string;
  readonly choice: string;
  readonly seed?: number | string;
  readonly version?: string;
  readonly extra?: readonly (string | number)[];
}

export interface StableIdOptions {
  readonly length?: number;
}

const DEFAULT_STABLE_SCOPE = "plan";
const DEFAULT_VERSION = "1.0.0";

export function stableId(input: StableIdInput, options: StableIdOptions = {}): string {
  const scope = input.scope ?? DEFAULT_STABLE_SCOPE;
  const seedValue = normalizeSeed(input.seed ?? 0);
  const version = input.version ?? DEFAULT_VERSION;
  const payload = [scope, `${input.specId}|${input.component}|${input.choice}|${seedValue}|${version}`];
  if (input.extra && input.extra.length > 0) {
    payload.push(...input.extra.map((value) => String(value)));
  }
  const hash = createHash("sha256");
  hash.update(payload.join(":"));
  const digest = hash.digest("hex");
  if (options.length && options.length > 0) {
    return digest.slice(0, options.length);
  }
  return digest;
}

export type DeepReadonly<T> = T extends (...args: never[]) => unknown
  ? T
  : T extends Array<infer U>
  ? ReadonlyArray<DeepReadonly<U>>
  : T extends object
  ? { readonly [K in keyof T]: DeepReadonly<T[K]> }
  : T;

export function deepFreeze<T>(value: T): DeepReadonly<T> {
  if (typeof value !== "object" || value === null) {
    return value as DeepReadonly<T>;
  }
  const object = value as Record<PropertyKey, unknown>;
  for (const key of Reflect.ownKeys(object)) {
    const nested = object[key as keyof typeof object];
    if (typeof nested === "object" && nested !== null) {
      deepFreeze(nested);
    }
  }
  return Object.freeze(value) as DeepReadonly<T>;
}

export function stableSort<T>(values: readonly T[], compare: (left: T, right: T) => number): T[] {
  return values
    .map((value, index) => ({ value, index }))
    .sort((left, right) => {
      const order = compare(left.value, right.value);
      if (order !== 0) {
        return order;
      }
      return left.index - right.index;
    })
    .map((entry) => entry.value);
}

export type Rng = () => number;

const UINT32_MAX = 0xffffffff;

function normalizeSeed(seed: number | string): number {
  if (typeof seed === "number" && Number.isFinite(seed)) {
    return seed >>> 0;
  }
  const hash = createHash("sha256");
  hash.update(String(seed));
  const buffer = hash.digest();
  return buffer.readUInt32BE(0);
}

export function seedRng(seed: number | string): Rng {
  let state = normalizeSeed(seed) || 1;
  return () => {
    state |= 0;
    state = (state + 0x6d2b79f5) | 0;
    let t = Math.imul(state ^ (state >>> 15), 1 | state);
    t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t;
    return ((t ^ (t >>> 14)) >>> 0) / (UINT32_MAX + 1);
  };
}

export function seededShuffle<T>(values: readonly T[], rng: Rng): T[] {
  const result = [...values];
  for (let i = result.length - 1; i > 0; i -= 1) {
    const j = Math.floor(rng() * (i + 1));
    const temp = result[i];
    result[i] = result[j];
    result[j] = temp;
  }
  return result;
}
