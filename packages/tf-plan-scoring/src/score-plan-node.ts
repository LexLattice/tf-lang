import type { Score } from "@tf-lang/tf-plan-core";
import { stableSort } from "@tf-lang/tf-plan-core";

import { complexity, depsReady, devTime, metricWeight, perf, risk } from "./metrics.js";
import type { MetricResult, ScoreContext, ScoreResult } from "./types.js";

const SCALE = 100;

function round(value: number, decimals = 2): number {
  const factor = 10 ** decimals;
  return Math.round((value + Number.EPSILON) * factor) / factor;
}

export function scorePlanNode(context: ScoreContext): ScoreResult {
  const metrics: MetricResult[] = [
    complexity(context),
    risk(context),
    perf(context),
    devTime(context),
    depsReady(context)
  ];

  const weightedSum = metrics.reduce((total, metric) => total + metric.value * metric.weight, 0);
  const totalScore = round(weightedSum * SCALE, 2);

  const explain = stableSort(metrics, (left, right) => left.metric.localeCompare(right.metric)).map((metric) => ({
    metric: metric.metric,
    value: round(metric.value * SCALE, 2),
    weight: metric.weight,
    rationale: metric.rationale
  }));

  const score: Score = {
    total: totalScore,
    complexity: round(metrics.find((metric) => metric.metric === "complexity")!.value * SCALE, 2),
    risk: round(metrics.find((metric) => metric.metric === "risk")!.value * SCALE, 2),
    perf: round(metrics.find((metric) => metric.metric === "perf")!.value * SCALE, 2),
    devTime: round(metrics.find((metric) => metric.metric === "devTime")!.value * SCALE, 2),
    depsReady: round(metrics.find((metric) => metric.metric === "depsReady")!.value * SCALE, 2),
    explain
  };

  return { score, metrics };
}

export { metricWeight } from "./metrics.js";
