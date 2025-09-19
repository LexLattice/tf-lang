import type { MetricResult, MetricName, ScoreContext } from "./types.js";

const METRIC_WEIGHTS: Record<MetricName, number> = {
  complexity: 0.2,
  risk: 0.25,
  perf: 0.2,
  devTime: 0.2,
  depsReady: 0.15
};

export function metricWeight(metric: MetricName): number {
  return METRIC_WEIGHTS[metric];
}

function clamp01(value: number): number {
  if (Number.isNaN(value)) {
    return 0;
  }
  return Math.min(1, Math.max(0, value));
}

function tokenize(text: string): string[] {
  return text
    .toLowerCase()
    .replace(/[^a-z0-9]+/g, " ")
    .split(" ")
    .map((token) => token.trim())
    .filter(Boolean);
}

function gatherKeywords(context: ScoreContext): Set<string> {
  const keywords = new Set<string>();
  for (const part of [context.component, context.choice]) {
    tokenize(part).forEach((token) => keywords.add(token));
  }
  const metaKeywords = context.metadata?.keywords ?? [];
  metaKeywords.forEach((token) => keywords.add(token.toLowerCase()));
  return keywords;
}

function hasKeyword(keywords: Set<string>, targets: readonly string[]): boolean {
  for (const target of targets) {
    if (keywords.has(target)) {
      return true;
    }
  }
  return false;
}

function keywordCount(keywords: Set<string>, targets: readonly string[]): number {
  let count = 0;
  for (const target of targets) {
    if (keywords.has(target)) {
      count += 1;
    }
  }
  return count;
}

export function complexity(context: ScoreContext): MetricResult {
  const keywords = gatherKeywords(context);
  const baseLoad = clamp01(context.metadata?.effort ?? Math.max(0, keywords.size - 2) / 6);
  const adjustments: string[] = [];
  let load = baseLoad;

  if (context.metadata?.maturity !== undefined) {
    const maturity = clamp01(context.metadata.maturity);
    const delta = maturity * 0.2;
    load = clamp01(load - delta);
    adjustments.push(`maturity ${maturity.toFixed(2)} reduces load by ${delta.toFixed(2)}`);
  }

  if (hasKeyword(keywords, ["simple", "basic", "starter"])) {
    load = clamp01(load - 0.15);
    adjustments.push("keyword simple/basic/starter implies lower complexity");
  }

  const heavyKeywords = keywordCount(keywords, ["distributed", "cluster", "microservices", "orchestration", "rewrite"]);
  if (heavyKeywords > 0) {
    const delta = Math.min(0.3, heavyKeywords * 0.12);
    load = clamp01(load + delta);
    adjustments.push(`architectural keywords add ${delta.toFixed(2)} to complexity load`);
  }

  const value = clamp01(1 - load);
  const rationale = [`baseline load ${baseLoad.toFixed(2)}`, ...adjustments].join("; ");
  return {
    metric: "complexity",
    value,
    weight: metricWeight("complexity"),
    rationale
  };
}

export function risk(context: ScoreContext): MetricResult {
  const keywords = gatherKeywords(context);
  const baseRisk = clamp01(context.metadata?.risk ?? 0.4);
  const adjustments: string[] = [];
  let riskScore = baseRisk;

  if (hasKeyword(keywords, ["experimental", "beta", "preview"])) {
    riskScore = clamp01(riskScore + 0.25);
    adjustments.push("keyword experimental/beta/preview increases risk");
  }

  if (hasKeyword(keywords, ["legacy", "rewrite", "migration"])) {
    riskScore = clamp01(riskScore + 0.2);
    adjustments.push("keyword legacy/rewrite/migration increases risk");
  }

  if (hasKeyword(keywords, ["safe", "battle", "proven", "stable"])) {
    riskScore = clamp01(riskScore - 0.15);
    adjustments.push("keyword safe/battle/proven/stable lowers risk");
  }

  const incidents = context.repoSignals?.incidentHistory ?? [];
  const relevant = incidents.filter((incident) => incident.component === context.component);
  if (relevant.length > 0) {
    const incidentPenalty = clamp01(
      Math.min(0.3, relevant.reduce((sum, entry) => sum + clamp01(entry.severity) * 0.1, 0))
    );
    riskScore = clamp01(riskScore + incidentPenalty);
    adjustments.push(`recent incidents add ${incidentPenalty.toFixed(2)} risk`);
  }

  const adoptionTrend = context.repoSignals?.adoptionTrend?.[context.choice];
  if (typeof adoptionTrend === "number" && !Number.isNaN(adoptionTrend)) {
    const delta = -0.1 * adoptionTrend;
    riskScore = clamp01(riskScore + delta);
    adjustments.push(`adoption trend ${adoptionTrend.toFixed(2)} adjusts risk by ${delta.toFixed(2)}`);
  }

  const value = clamp01(1 - riskScore);
  const rationale = [`baseline risk ${baseRisk.toFixed(2)}`, ...adjustments].join("; ");
  return {
    metric: "risk",
    value,
    weight: metricWeight("risk"),
    rationale
  };
}

export function perf(context: ScoreContext): MetricResult {
  const keywords = gatherKeywords(context);
  const basePerf = clamp01(context.metadata?.performance ?? 0.55);
  const adjustments: string[] = [];
  let perfScore = basePerf;

  if (hasKeyword(keywords, ["fast", "vector", "async", "batch", "parallel"])) {
    perfScore = clamp01(perfScore + 0.2);
    adjustments.push("keywords fast/vector/async/batch/parallel boost perf");
  }

  if (hasKeyword(keywords, ["cache", "optimize", "accelerated"])) {
    perfScore = clamp01(perfScore + 0.15);
    adjustments.push("keywords cache/optimize/accelerated boost perf");
  }

  if (hasKeyword(keywords, ["basic", "simple", "prototype", "mock"])) {
    perfScore = clamp01(perfScore - 0.1);
    adjustments.push("keywords basic/simple/prototype/mock reduce perf expectations");
  }

  const value = clamp01(perfScore);
  const rationale = [`baseline perf ${basePerf.toFixed(2)}`, ...adjustments].join("; ");
  return {
    metric: "perf",
    value,
    weight: metricWeight("perf"),
    rationale
  };
}

export function devTime(context: ScoreContext): MetricResult {
  const keywords = gatherKeywords(context);
  const velocity = clamp01(context.repoSignals?.componentVelocity?.[context.component] ?? 0.5);
  const baseTime = clamp01(context.metadata?.timeToDeliver ?? (1 - velocity));
  const adjustments: string[] = [];
  let deliveryTime = baseTime;

  if (hasKeyword(keywords, ["quick", "rapid", "starter", "template"])) {
    deliveryTime = clamp01(deliveryTime - 0.2);
    adjustments.push("keywords quick/rapid/starter/template reduce delivery time");
  }

  if (hasKeyword(keywords, ["rewrite", "migration", "greenfield"])) {
    deliveryTime = clamp01(deliveryTime + 0.25);
    adjustments.push("keywords rewrite/migration/greenfield increase delivery time");
  }

  if (context.metadata?.effort !== undefined) {
    const delta = clamp01(context.metadata.effort) * 0.3;
    deliveryTime = clamp01(deliveryTime + delta);
    adjustments.push(`effort signal adds ${delta.toFixed(2)} delivery time`);
  }

  const value = clamp01(1 - deliveryTime);
  const rationale = [`baseline delivery time ${baseTime.toFixed(2)}`, ...adjustments].join("; ");
  return {
    metric: "devTime",
    value,
    weight: metricWeight("devTime"),
    rationale
  };
}

export function depsReady(context: ScoreContext): MetricResult {
  const dependencies = context.metadata?.dependencies ?? [];
  const signals = context.repoSignals?.dependencyHealth ?? {};
  const base = dependencies.length === 0 ? 0.75 : 0.5;
  let readiness = base;
  const adjustments: string[] = [];

  if (dependencies.length > 0) {
    const scores = dependencies.map((dep) => clamp01(signals[dep] ?? 0.5));
    const avg = scores.reduce((sum, value) => sum + value, 0) / scores.length;
    readiness = clamp01((readiness + avg) / 2);
    adjustments.push(`dependency readiness average ${avg.toFixed(2)}`);
  }

  const adoptionTrend = context.repoSignals?.adoptionTrend?.[context.choice];
  if (typeof adoptionTrend === "number") {
    const delta = adoptionTrend * 0.1;
    readiness = clamp01(readiness + delta);
    adjustments.push(`adoption trend ${adoptionTrend.toFixed(2)} shifts readiness by ${delta.toFixed(2)}`);
  }

  if (context.metadata?.maturity !== undefined) {
    const delta = clamp01(context.metadata.maturity) * 0.1;
    readiness = clamp01(readiness + delta);
    adjustments.push(`maturity contributes ${delta.toFixed(2)} readiness`);
  }

  const value = clamp01(readiness);
  const rationale = [`baseline readiness ${base.toFixed(2)}`, ...adjustments].join("; ");
  return {
    metric: "depsReady",
    value,
    weight: metricWeight("depsReady"),
    rationale
  };
}
