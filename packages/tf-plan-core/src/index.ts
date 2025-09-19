import { createHash } from 'node:crypto';
import { readFileSync } from 'node:fs';
import { fileURLToPath } from 'node:url';
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

export function resolveSchemaPath(name: string): URL {
  return new URL(`./schema/${name}`, import.meta.url);
}

const schemaCache = new Map<string, Readonly<Record<string, unknown>>>();

function loadSchema(name: string): Readonly<Record<string, unknown>> {
  const cached = schemaCache.get(name);
  if (cached) return cached;

  const url = resolveSchemaPath(name);
  try {
    const filePath = fileURLToPath(url);
    const raw = readFileSync(filePath, 'utf8');
    const parsed = JSON.parse(raw) as Record<string, unknown>;
    const frozen = deepFreeze(parsed);
    schemaCache.set(name, frozen);
    return frozen;
  } catch (error) {
    const reason = (error as Error)?.message ?? String(error);
    throw new Error(`Unable to load schema ${name} at ${url.toString()}: ${reason}`);
  }
}

const ajv = new Ajv({ allErrors: true, strict: true });

export const TF_BRANCH_SCHEMA = loadSchema('tf-branch.schema.json');
export const TF_PLAN_SCHEMA = loadSchema('tf-plan.schema.json');
export const TF_COMPARE_SCHEMA = loadSchema('tf-compare.schema.json');

ajv.addSchema(TF_BRANCH_SCHEMA, 'tf-branch.schema.json');
ajv.addSchema(TF_PLAN_SCHEMA, 'tf-plan.schema.json');
ajv.addSchema(TF_COMPARE_SCHEMA, 'tf-compare.schema.json');

const planValidator = ajv.compile<PlanGraph>(TF_PLAN_SCHEMA);
const branchValidator = ajv.compile<PlanNode>(TF_BRANCH_SCHEMA);
const compareValidator = ajv.compile<unknown>(TF_COMPARE_SCHEMA);

function formatAjvErrors(errors: ErrorObject[] | null | undefined): string {
  if (!errors || errors.length === 0) {
    return 'unknown schema validation error';
  }

  return errors
    .map((error) => {
      const instancePath = error.instancePath || '/';
      return `${instancePath} ${error.message ?? 'is invalid'}`;
    })
    .join(', ');
}

function enforceValidation<T>(
  value: unknown,
  validator: ValidateFunction<T>,
  label: string,
): T {
  if (!validator(value)) {
    const detail = formatAjvErrors(validator.errors ?? null);
    throw new Error(`${label} validation failed: ${detail}`);
  }

  return value as T;
}

export function validateBranch(value: unknown): PlanNode {
  return enforceValidation(value, branchValidator, 'Plan branch');
}

export function validatePlan(value: unknown): PlanGraph {
  const plan = enforceValidation(value, planValidator, 'Plan graph');
  plan.nodes.forEach((node, index) => {
    try {
      enforceValidation(node, branchValidator, `Plan node at index ${index}`);
    } catch (error) {
      const nodeId = (node as { nodeId?: string }).nodeId ?? '<unknown>';
      throw new Error(`Plan node ${nodeId} failed validation: ${(error as Error).message}`);
    }
  });
  return plan;
}

export function validateCompare<T>(value: unknown): T {
  return enforceValidation(value, compareValidator as ValidateFunction<T>, 'Compare report');
}

/**
 * Parse and validate a specId of the form "<name>:<8 hex>".
 */
export function parseSpecId(specId: string): { specHash: string } {
  if (typeof specId !== 'string' || specId.length === 0) {
    throw new Error(`Invalid specId: expected non-empty string, received ${String(specId)}`);
  }
  const idx = specId.lastIndexOf(':');
  if (idx <= 0 || idx === specId.length - 1) {
    throw new Error(
      `Invalid specId '${specId}': expected format '<name>:<8 hex>' with a single colon separator.`,
    );
  }
  const hash = specId.slice(idx + 1);
  if (!/^[0-9a-f]{8}$/.test(hash)) {
    throw new Error(
      `Invalid specId '${specId}': hash part must be 8 lowercase hex characters.`,
    );
  }
  return { specHash: hash } as const;
}
