import { createHash } from 'node:crypto';
import { createRequire } from 'node:module';
import Ajv, { type ErrorObject, type ValidateFunction } from 'ajv';

export const PLAN_GRAPH_VERSION = '0.1.0';

export interface Score {
  readonly total: number;
  readonly complexity: number;
  readonly risk: number;
  readonly perf: number;
  readonly devTime: number;
  readonly depsReady: number;
  readonly explain: readonly string[];
}

export interface PlanNode {
  readonly nodeId: string;
  readonly specId: string;
  readonly component: string;
  readonly choice: string;
  readonly deps: readonly string[];
  readonly rationale: string;
  readonly score: Score;
}

export interface PlanEdge {
  readonly from: string;
  readonly to: string;
  readonly kind: 'depends' | 'sequence';
}

export interface PlanGraphMeta {
  readonly seed: number;
  readonly specHash: string;
  readonly version: string;
}

export interface PlanGraph {
  readonly version: string;
  readonly nodes: readonly PlanNode[];
  readonly edges: readonly PlanEdge[];
  readonly meta: PlanGraphMeta;
}

export interface StableIdInput {
  readonly scope: string;
  readonly specId: string;
  readonly component: string;
  readonly choice: string;
  readonly seed: number;
  readonly version: string;
}

export interface StableIdResult {
  readonly full: string;
  readonly short: string;
}

export function stableId(input: StableIdInput): StableIdResult {
  const canonical = `${input.scope}:${input.specId}|${input.component}|${input.choice}|${input.seed}|${input.version}`;
  const full = createHash('sha256').update(canonical).digest('hex');
  return {
    full,
    short: full.slice(0, 12),
  };
}

export function deepFreeze<T>(value: T): Readonly<T> {
  if (value === null) {
    return value as Readonly<T>;
  }

  if (typeof value !== 'object') {
    return value as Readonly<T>;
  }

  const seen = new Set<unknown>();

  const freeze = (target: unknown): unknown => {
    if (target === null || typeof target !== 'object') {
      return target;
    }

    if (seen.has(target)) {
      return target;
    }

    seen.add(target);

    if (Array.isArray(target)) {
      for (const item of target) {
        freeze(item);
      }
    } else {
      const entries = Object.entries(target as Record<string, unknown>);
      for (const [, entryValue] of entries) {
        freeze(entryValue);
      }
    }

    return Object.freeze(target);
  };

  return freeze(value) as Readonly<T>;
}

export type Comparator<T> = (a: T, b: T) => number;

export function stableSort<T>(items: readonly T[], compare: Comparator<T>): T[] {
  return items
    .map((value, index) => ({ value, index }))
    .sort((left, right) => {
      const result = compare(left.value, right.value);
      if (result !== 0) {
        return result;
      }
      return left.index - right.index;
    })
    .map((entry) => entry.value);
}

function normalizeSeed(seed: number | string): number {
  if (typeof seed === 'number' && Number.isFinite(seed)) {
    return seed >>> 0;
  }

  const text = typeof seed === 'string' ? seed : JSON.stringify(seed);
  const hash = createHash('sha256').update(text).digest();
  return hash.readUInt32BE(0);
}

export interface SeededRng {
  next(): number;
  nextInt(maxExclusive: number): number;
}

export function seedRng(seed: number | string): SeededRng {
  let state = normalizeSeed(seed) || 1;

  const next = (): number => {
    // Mulberry32 PRNG
    state |= 0;
    state = (state + 0x6D2B79F5) | 0;
    let t = Math.imul(state ^ (state >>> 15), 1 | state);
    t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t;
    return ((t ^ (t >>> 14)) >>> 0) / 0x100000000;
  };

  return {
    next,
    nextInt(maxExclusive: number) {
      if (!Number.isFinite(maxExclusive) || maxExclusive <= 0) {
        throw new Error(`maxExclusive must be a positive finite number, received ${maxExclusive}`);
      }
      return Math.floor(next() * maxExclusive);
    },
  };
}

export function canonicalStringify(value: unknown): string {
  const serialize = (input: unknown): string => {
    if (input === null || typeof input !== 'object') {
      return JSON.stringify(input);
    }

    if (Array.isArray(input)) {
      const items = input.map((element) => serialize(element));
      return `[${items.join(',')}]`;
    }

    const entries = Object.entries(input as Record<string, unknown>);
    entries.sort((left, right) => {
      if (left[0] < right[0]) {
        return -1;
      }
      if (left[0] > right[0]) {
        return 1;
      }
      return 0;
    });

    const parts = entries.map(([key, val]) => `${JSON.stringify(key)}:${serialize(val)}`);
    return `{${parts.join(',')}}`;
  };

  return serialize(value);
}

export function hashObject(value: unknown): string {
  const canonical = canonicalStringify(value);
  return createHash('sha256').update(canonical).digest('hex');
}

export type RepoSignals = Readonly<Record<string, unknown>>;

const require = createRequire(import.meta.url);

function loadSchema(name: string): Record<string, unknown> {
  const candidates = [`../../../schema/${name}`, `../../../../schema/${name}`];
  for (const candidate of candidates) {
    try {
      return require(candidate);
    } catch {
      continue;
    }
  }
  throw new Error(`Unable to load schema ${name}`);
}

function formatErrors(errors: ErrorObject[] | null | undefined): string {
  if (!errors || errors.length === 0) {
    return 'unknown error';
  }
  return errors
    .map((error) => {
      const instance = error.instancePath || '/';
      const message = error.message ?? 'validation error';
      return `${instance} ${message}`;
    })
    .join(', ');
}

function assertValid<T>(value: unknown, validator: ValidateFunction<T>, label: string): T {
  if (validator(value)) {
    return value;
  }
  const details = formatErrors(validator.errors);
  throw new Error(`${label} failed validation: ${details}`);
}

const branchSchema = loadSchema('tf-branch.schema.json');
const planSchema = loadSchema('tf-plan.schema.json');
const compareSchema = loadSchema('tf-compare.schema.json');

export const tfSchemas = Object.freeze({
  branch: branchSchema,
  plan: planSchema,
  compare: compareSchema,
});

const ajv = new Ajv({ allErrors: true, strict: true });
ajv.addSchema(branchSchema, 'tf-branch.schema.json');

const validatePlanGraphFn = ajv.compile<PlanGraph>(planSchema);
const validatePlanNodeFn = ajv.compile<PlanNode>(branchSchema);
const validateCompareFn = ajv.compile<unknown>(compareSchema);

export function validateBranch(value: unknown): PlanNode {
  return assertValid<PlanNode>(value, validatePlanNodeFn, 'Plan node');
}

export function validatePlan(value: unknown): PlanGraph {
  const plan = assertValid<PlanGraph>(value, validatePlanGraphFn, 'Plan graph');
  plan.nodes.forEach((node) => {
    validateBranch(node);
  });
  return plan;
}

export function validateCompare<T>(value: unknown): T {
  return assertValid<T>(value, validateCompareFn as ValidateFunction<T>, 'Compare report');
}
