import type { ScoreBreakdown } from "@tf-lang/tf-plan-core";
import type { ComponentSignals, MetricName, RepoSignals, ScoreContext, ScoreDetail } from "./types.js";

const KEYWORD_WEIGHTS: Record<MetricName, Record<string, number>> = {
  complexity: {
    simple: 1.5,
    basic: 1,
    lite: 1,
    managed: 0.75,
    distributed: -2,
    cluster: -2,
    enterprise: -1.5,
    advanced: -2,
  },
  risk: {
    experimental: 2.5,
    beta: 2,
    preview: 1.5,
    legacy: 1,
    deprecated: 3,
    stable: -1,
    ga: -1.5,
    lts: -2,
  },
  perf: {
    optimized: 2,
    compiled: 2.5,
    vector: 1,
    async: 0.5,
    cache: 0.5,
    wasm: 1.5,
    serverless: 0.75,
  },
  devTime: {
    migration: 2,
    rewrite: 2.5,
    bootstrap: -1,
    scaffold: -1.5,
    template: -1,
    managed: -0.75,
  },
  depsReady: {
    preview: -1.5,
    beta: -1,
    ga: 1.5,
    stable: 1,
    managed: 0.5,
    proven: 1,
  },
};

function clamp(value: number, min: number, max: number): number {
  return Math.min(max, Math.max(min, value));
}

function componentSignals(repoSignals: RepoSignals | undefined, component: string): ComponentSignals | undefined {
  return repoSignals?.componentSignals?.[component];
}

function normalized(value: number | undefined, fallback: number): number {
  if (typeof value !== "number" || Number.isNaN(value)) {
    return fallback;
  }
  return clamp(value, 0, 1);
}

function applyKeywordWeights(metric: MetricName, choice: string, tags: readonly string[] | undefined): number {
  const weights = KEYWORD_WEIGHTS[metric];
  const haystacks = [choice.toLowerCase(), ...(tags?.map((tag) => tag.toLowerCase()) ?? [])];
  let total = 0;
  for (const [keyword, weight] of Object.entries(weights)) {
    for (const haystack of haystacks) {
      if (haystack.includes(keyword)) {
        total += weight;
        break;
      }
    }
  }
  return total;
}

function applyHeuristics(context: ScoreContext, metric: MetricName): number {
  return context.metadata?.heuristics?.[metric] ?? 0;
}

function describe(adjustments: readonly string[], baseExplanation: string): string {
  const details = adjustments.filter(Boolean);
  if (details.length === 0) {
    return baseExplanation;
  }
  return `${baseExplanation}: ${details.join(", ")}`;
}

export function complexity(context: ScoreContext): ScoreDetail {
  const tags = context.metadata?.tags;
  const adjustments: string[] = [];
  let value = 6 + applyKeywordWeights("complexity", context.choice, tags);
  const heur = applyHeuristics(context, "complexity");
  if (heur !== 0) {
    value += heur;
    adjustments.push(`heuristic ${heur.toFixed(2)}`);
  }
  const signals = componentSignals(context.repoSignals, context.component);
  if (signals?.velocity !== undefined) {
    const adjustment = (0.5 - normalized(signals.velocity, 0.5)) * 4;
    value += adjustment;
    adjustments.push(`velocity influence ${adjustment.toFixed(2)}`);
  }
  if (signals?.stability !== undefined) {
    const adjustment = (normalized(signals.stability, 0.5) - 0.5) * 3;
    value += adjustment;
    adjustments.push(`stability ${adjustment.toFixed(2)}`);
  }
  value = clamp(value, 0, 10);
  return {
    value,
    explanation: describe(adjustments, `complexity profile ${value.toFixed(2)}`),
  };
}

export function risk(context: ScoreContext): ScoreDetail {
  const tags = context.metadata?.tags;
  const adjustments: string[] = [];
  let value = 4 + applyKeywordWeights("risk", context.choice, tags);
  const heur = applyHeuristics(context, "risk");
  if (heur !== 0) {
    value += heur;
    adjustments.push(`heuristic ${heur.toFixed(2)}`);
  }
  const signals = componentSignals(context.repoSignals, context.component);
  if (signals?.incidents !== undefined) {
    const adjustment = normalized(signals.incidents, 0) * 3;
    value += adjustment;
    adjustments.push(`incidents ${adjustment.toFixed(2)}`);
  }
  if (signals?.stability !== undefined) {
    const adjustment = (0.5 - normalized(signals.stability, 0.5)) * 4;
    value += adjustment;
    adjustments.push(`stability delta ${adjustment.toFixed(2)}`);
  }
  const floor = normalized(context.repoSignals?.global?.riskFloor, 0);
  if (value < floor * 10) {
    adjustments.push(`risk floor ${floor.toFixed(2)}`);
    value = floor * 10;
  }
  value = clamp(value, 0, 10);
  return {
    value,
    explanation: describe(adjustments, `risk profile ${value.toFixed(2)}`),
  };
}

export function perf(context: ScoreContext): ScoreDetail {
  const tags = context.metadata?.tags;
  const adjustments: string[] = [];
  let value = 5 + applyKeywordWeights("perf", context.choice, tags);
  const heur = applyHeuristics(context, "perf");
  if (heur !== 0) {
    value += heur;
    adjustments.push(`heuristic ${heur.toFixed(2)}`);
  }
  const signals = componentSignals(context.repoSignals, context.component);
  if (signals?.performance !== undefined) {
    const adjustment = (normalized(signals.performance, 0.5) - 0.5) * 5;
    value += adjustment;
    adjustments.push(`performance metric ${adjustment.toFixed(2)}`);
  }
  value = clamp(value, 0, 10);
  return {
    value,
    explanation: describe(adjustments, `performance outlook ${value.toFixed(2)}`),
  };
}

export function devTime(context: ScoreContext): ScoreDetail {
  const tags = context.metadata?.tags;
  const adjustments: string[] = [];
  let value = 4 + applyKeywordWeights("devTime", context.choice, tags);
  const heur = applyHeuristics(context, "devTime");
  if (heur !== 0) {
    value += heur;
    adjustments.push(`heuristic ${heur.toFixed(2)}`);
  }
  const signals = componentSignals(context.repoSignals, context.component);
  if (signals?.velocity !== undefined) {
    const adjustment = (0.5 - normalized(signals.velocity, 0.5)) * 4;
    value += adjustment;
    adjustments.push(`velocity ${adjustment.toFixed(2)}`);
  }
  value = clamp(value, 0, 10);
  return {
    value,
    explanation: describe(adjustments, `dev time estimate ${value.toFixed(2)}`),
  };
}

export function depsReady(context: ScoreContext): ScoreDetail {
  const tags = context.metadata?.tags;
  const adjustments: string[] = [];
  let value = 5 + applyKeywordWeights("depsReady", context.choice, tags);
  const heur = applyHeuristics(context, "depsReady");
  if (heur !== 0) {
    value += heur;
    adjustments.push(`heuristic ${heur.toFixed(2)}`);
  }
  const signals = componentSignals(context.repoSignals, context.component);
  if (signals?.readiness !== undefined) {
    const adjustment = (normalized(signals.readiness, 0.5) - 0.5) * 5;
    value += adjustment;
    adjustments.push(`readiness ${adjustment.toFixed(2)}`);
  }
  value = clamp(value, 0, 10);
  return {
    value,
    explanation: describe(adjustments, `dependency readiness ${value.toFixed(2)}`),
  };
}

export function scorePlanNode(context: ScoreContext): ScoreBreakdown {
  const complexityDetail = complexity(context);
  const riskDetail = risk(context);
  const perfDetail = perf(context);
  const devTimeDetail = devTime(context);
  const depsReadyDetail = depsReady(context);

  const positive = (complexityDetail.value + perfDetail.value + depsReadyDetail.value) / 3;
  const negative = (riskDetail.value + devTimeDetail.value) / 2;
  const total = positive - negative;

  return {
    total,
    complexity: complexityDetail.value,
    risk: riskDetail.value,
    perf: perfDetail.value,
    devTime: devTimeDetail.value,
    depsReady: depsReadyDetail.value,
    explain: [
      complexityDetail.explanation,
      perfDetail.explanation,
      depsReadyDetail.explanation,
      riskDetail.explanation,
      devTimeDetail.explanation,
    ],
  };
}
