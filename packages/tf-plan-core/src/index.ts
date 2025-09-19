import { createHash } from 'node:crypto';
import { createRequire } from 'node:module';
import Ajv, { type ErrorObject } from 'ajv';

const require = createRequire(import.meta.url);

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

const schemaCache = new Map<string, Readonly<Record<string, unknown>>>();

function loadSchema(name: string): Readonly<Record<string, unknown>> {
  const cached = schemaCache.get(name);
  if (cached) {
    return cached;
  }

  const candidates = [
    `../../../schema/${name}`,
    `../../../../schema/${name}`,
  ];

  for (const candidate of candidates) {
    try {
      const schema = require(candidate) as Record<string, unknown>;
      const frozen = deepFreeze(schema);
      schemaCache.set(name, frozen);
      return frozen;
    } catch {
      continue;
    }
  }

  throw new Error(`Unable to load schema ${name}`);
}

function formatErrors(errors: readonly ErrorObject[] | null | undefined): string {
  if (!errors || errors.length === 0) {
    return 'unknown error';
  }
  return errors
    .map((error) => {
      const path = error.instancePath && error.instancePath.length > 0 ? error.instancePath : '/';
      return `${path} ${error.message ?? 'validation failed'}`.trim();
    })
    .join('; ');
}

const ajv = new Ajv({ allErrors: true, strict: true });

const planSchemaInternal = loadSchema('tf-plan.schema.json');
const branchSchemaInternal = loadSchema('tf-branch.schema.json');
const compareSchemaInternal = loadSchema('tf-compare.schema.json');

ajv.addSchema(branchSchemaInternal, 'https://tf-lang.dev/schema/tf-branch.schema.json');
ajv.addSchema(branchSchemaInternal, 'tf-branch.schema.json');
ajv.addSchema(compareSchemaInternal, 'https://tf-lang.dev/schema/tf-compare.schema.json');

const validatePlanNodeInternal = ajv.compile<PlanNode>(branchSchemaInternal);
const validateCompareInternal = ajv.compile<unknown>(compareSchemaInternal);
const validatePlanGraphInternal = ajv.compile<PlanGraph>(planSchemaInternal);

export const planSchema = planSchemaInternal;
export const branchSchema = branchSchemaInternal;
export const compareSchema = compareSchemaInternal;

export function validateBranch(node: PlanNode, context = 'plan node'): PlanNode {
  if (!validatePlanNodeInternal(node)) {
    const message = formatErrors(validatePlanNodeInternal.errors);
    throw new Error(`${context} failed validation: ${message}`);
  }
  return node;
}

export function validatePlan(plan: PlanGraph, context = 'plan graph'): PlanGraph {
  if (!validatePlanGraphInternal(plan)) {
    const message = formatErrors(validatePlanGraphInternal.errors);
    throw new Error(`${context} failed validation: ${message}`);
  }

  plan.nodes.forEach((node, index) => {
    const label = `${context}.nodes[${index}]`;
    validateBranch(node, label);
  });

  return plan;
}

export function validateCompare<T>(report: T, context = 'compare report'): T {
  if (!validateCompareInternal(report as unknown)) {
    const message = formatErrors(validateCompareInternal.errors);
    throw new Error(`${context} failed validation: ${message}`);
  }
  return report;
}
