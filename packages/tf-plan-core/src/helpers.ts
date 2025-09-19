import { createHash } from "node:crypto";
import { canonicalJson } from "@tf-lang/utils";
import type {
  PlanGraph,
  ScoreAggregateOptions,
  ScoreBreakdown,
  SeededRng,
  StableIdInput,
} from "./types.js";

export function stableId(input: StableIdInput): string {
  const payload = `${input.scope}:${input.specId}|${input.component}|${input.choice}|${input.seed}|${input.version}`;
  return hashString(payload);
}

export function shortId(id: string): string {
  return id.slice(0, 12);
}

export function hashString(value: string): string {
  return createHash("sha256").update(value).digest("hex");
}

export function hashObject(value: unknown): string {
  return hashString(canonicalJson(value));
}

export function deepFreeze<T>(value: T): T {
  if (typeof value !== "object" || value === null) {
    return value;
  }
  if (Array.isArray(value)) {
    value.forEach((item) => deepFreeze(item));
  } else {
    Object.getOwnPropertyNames(value).forEach((key) => {
      const descriptor = Object.getOwnPropertyDescriptor(value, key);
      if (descriptor && "value" in descriptor) {
        deepFreeze((value as Record<string, unknown>)[key]);
      }
    });
  }
  return Object.freeze(value);
}

export function stableSort<T>(items: readonly T[], compare: (a: T, b: T) => number): T[] {
  return items
    .map((value, index) => ({ value, index }))
    .sort((a, b) => {
      const result = compare(a.value, b.value);
      if (result !== 0) {
        return result;
      }
      return a.index - b.index;
    })
    .map((entry) => entry.value);
}

export function createSeededRng(seed: number | string): SeededRng {
  const normalizedSeed = typeof seed === "number" ? seed : Number.parseInt(hashString(seed).slice(0, 12), 16);
  let state = normalizedSeed >>> 0;

  const generator = () => {
    state = (state + 0x6d2b79f5) >>> 0;
    let t = state;
    t = Math.imul(t ^ (t >>> 15), t | 1);
    t ^= t + Math.imul(t ^ (t >>> 7), t | 61);
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  };

  return {
    next: () => generator(),
    integer: (maxExclusive: number) => {
      if (!Number.isFinite(maxExclusive) || maxExclusive <= 0) {
        throw new Error(`maxExclusive must be positive, received ${maxExclusive}`);
      }
      return Math.floor(generator() * maxExclusive);
    },
  };
}

export function aggregateScores(scores: readonly ScoreBreakdown[], options: ScoreAggregateOptions = {}): ScoreBreakdown {
  const weights = {
    complexity: 0.2,
    risk: 0.2,
    perf: 0.2,
    devTime: 0.2,
    depsReady: 0.2,
    ...options.weights,
  };

  const totals = scores.reduce(
    (acc, score) => {
      acc.complexity += score.complexity;
      acc.risk += score.risk;
      acc.perf += score.perf;
      acc.devTime += score.devTime;
      acc.depsReady += score.depsReady;
      acc.explain.push(...score.explain);
      return acc;
    },
    {
      complexity: 0,
      risk: 0,
      perf: 0,
      devTime: 0,
      depsReady: 0,
      explain: [] as string[],
    }
  );

  const weightSum =
    weights.complexity + weights.risk + weights.perf + weights.devTime + weights.depsReady;

  const total =
    (totals.complexity * weights.complexity +
      totals.perf * weights.perf +
      totals.depsReady * weights.depsReady) /
      weightSum -
    (totals.risk * weights.risk + totals.devTime * weights.devTime) / weightSum;

  return {
    total,
    complexity: totals.complexity,
    risk: totals.risk,
    perf: totals.perf,
    devTime: totals.devTime,
    depsReady: totals.depsReady,
    explain: totals.explain,
  };
}

export function freezePlanGraph<T extends PlanGraph>(graph: T): T {
  graph.nodes.forEach((node) => deepFreeze(node));
  graph.edges.forEach((edge) => deepFreeze(edge));
  return deepFreeze(graph);
}
