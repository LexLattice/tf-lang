import { createHash } from 'node:crypto';

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
  readonly nodes: readonly PlanNode[];
  readonly edges: readonly PlanEdge[];
  readonly meta: PlanGraphMeta;
}

export interface StableIdInput {
  readonly specId: string;
  readonly component: string;
  readonly choice: string;
  readonly seed: number | string;
  readonly version: string;
  readonly scope?: string;
}

export function stableId(input: StableIdInput): string {
  const scope = input.scope ?? 'scope';
  const payload = `${scope}:${input.specId}|${input.component}|${input.choice}|${String(
    input.seed,
  )}|${input.version}`;
  const hash = createHash('sha256').update(payload).digest('hex');
  return hash;
}

export function deepFreeze<T>(value: T): T {
  if (value && typeof value === 'object') {
    const properties = Reflect.ownKeys(value as object);
    for (const key of properties) {
      const descriptor = Reflect.getOwnPropertyDescriptor(value as object, key);
      if (!descriptor || typeof descriptor.value === 'undefined') {
        continue;
      }
      const child = descriptor.value;
      if (child && typeof child === 'object') {
        deepFreeze(child);
      }
    }
    Object.freeze(value);
  }
  return value;
}

export function stableSort<T>(values: readonly T[], compare: (a: T, b: T) => number): T[] {
  const annotated = values.map((value, index) => ({ value, index }));
  annotated.sort((a, b) => {
    const order = compare(a.value, b.value);
    if (order !== 0) {
      return order;
    }
    return a.index - b.index;
  });
  return annotated.map((entry) => entry.value);
}

export interface SeedRng {
  readonly seed: number;
  next(): number;
  nextInt(minInclusive: number, maxExclusive: number): number;
  pick<T>(values: readonly T[]): T;
}

function normalizeSeed(seed: number | string): number {
  if (typeof seed === 'number') {
    return seed >>> 0;
  }
  const digest = createHash('sha256').update(seed).digest('hex');
  return parseInt(digest.slice(0, 8), 16) >>> 0;
}

export function seedRng(seed: number | string): SeedRng {
  let state = normalizeSeed(seed) || 0x1a2b3c4d;
  const next = () => {
    // Mulberry32 implementation
    state |= 0;
    state = (state + 0x6d2b79f5) | 0;
    let t = Math.imul(state ^ (state >>> 15), 1 | state);
    t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t;
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  };
  return {
    seed: state >>> 0,
    next,
    nextInt(minInclusive: number, maxExclusive: number) {
      if (maxExclusive <= minInclusive) {
        throw new Error('Invalid range for nextInt');
      }
      const range = maxExclusive - minInclusive;
      return Math.floor(next() * range) + minInclusive;
    },
    pick<T>(values: readonly T[]): T {
      if (values.length === 0) {
        throw new Error('Cannot pick from empty array');
      }
      const index = Math.floor(next() * values.length);
      return values[index];
    },
  };
}

function canonicalize(value: unknown): string {
  if (value === null || typeof value !== 'object') {
    return JSON.stringify(value);
  }
  if (Array.isArray(value)) {
    const items = value.map((item) => canonicalize(item));
    return `[${items.join(',')}]`;
  }
  const entries = Object.entries(value as Record<string, unknown>)
    .map(([key, val]) => [key, canonicalize(val)] as const)
    .sort(([a], [b]) => (a < b ? -1 : a > b ? 1 : 0));
  return `{${entries.map(([key, val]) => `${JSON.stringify(key)}:${val}`).join(',')}}`;
}

export function computeSpecHash(spec: unknown): string {
  const json = canonicalize(spec);
  return createHash('sha256').update(json).digest('hex');
}

export function createScore(input: Omit<Score, 'total'>): Score {
  const explain = input.explain.slice().map((line) => line.trim()).filter((line) => line.length > 0);
  const total =
    input.complexity +
    input.perf +
    input.depsReady -
    input.risk -
    input.devTime;
  const score: Score = {
    total,
    complexity: input.complexity,
    risk: input.risk,
    perf: input.perf,
    devTime: input.devTime,
    depsReady: input.depsReady,
    explain,
  };
  return deepFreeze(score);
}

export function freezePlanGraph<T extends PlanGraph>(graph: T): T {
  graph.nodes.forEach((node) => deepFreeze(node));
  graph.edges.forEach((edge) => deepFreeze(edge));
  return deepFreeze(graph);
}
