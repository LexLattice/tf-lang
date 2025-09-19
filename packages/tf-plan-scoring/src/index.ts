import { RepoSignals, Score, seedRng } from '@tf-lang/tf-plan-core';

type Dimension = 'complexity' | 'risk' | 'perf' | 'devTime' | 'depsReady';

export interface DimensionScore {
  readonly value: number;
  readonly reason: string;
}

export interface ScoreContext {
  readonly component: string;
  readonly choice: string;
  readonly seed: number;
  readonly repoSignals?: RepoSignals;
}

const DIMENSION_WEIGHTS: Readonly<Record<Dimension, number>> = {
  perf: 0.35,
  depsReady: 0.2,
  complexity: 0.15,
  devTime: 0.15,
  risk: 0.15,
};

const COMPLEXITY_BASE = 4.5; // Baseline complexity for any component-choice pair.
const MANAGED_COMPLEXITY_DELTA = -1.2; // Managed offerings reduce perceived complexity.
const RISK_BASE = 3.5; // Neutral risk before keyword adjustments.
const RISK_BETA_PENALTY = 3.2; // Beta/experimental features increase risk substantially.
const RISK_LEGACY_PENALTY = 2.1; // Legacy migrations add additional risk.
const RISK_MANAGED_BONUS = -1.3; // Managed services tend to be safer.
const RISK_NETWORK_PENALTY = 0.4; // Network components skew slightly riskier.
const PERF_BASE = 6; // Neutral performance expectation.
const PERF_ACCELERATED_BONUS = 1.8; // Accelerated keywords imply higher performance.
const PERF_COST_PENALTY = -1.5; // Cost optimisations usually trade off performance.
const PERF_COMPUTE_BONUS = 0.6; // Compute-centric components deliver better throughput.
const PERF_TRANSFER_PENALTY = -0.3; // Transfer heavy workloads trend slower.
const DEV_TIME_BASE = 5; // Neutral development time in weeks.
const AUTOMATION_BONUS = -1.0; // Managed automation reduces development time.
const READINESS_READY = 9.5; // Repo signals marking ready imply high readiness.
const READINESS_BLOCKED = 2.5; // Blocked signals drastically reduce readiness.
const READINESS_EXISTING = 8.5; // Existing or reusable assets.
const READINESS_NEW = 4.5; // New prototypes less ready.
const READINESS_DEFAULT = 6.5; // Neutral readiness when no signals apply.
const TOKEN_SPLIT = /[^a-z0-9]+/i;

function assertFinite(value: number, label: string): number {
  if (!Number.isFinite(value)) {
    throw new Error(`${label} must be a finite number, received ${value}`);
  }
  return value;
}

function clampScore(value: number, label: string): number {
  const bounded = Math.min(10, Math.max(0, assertFinite(value, label)));
  return Number.parseFloat(bounded.toFixed(3));
}

function keywordFactor(text: string, keywords: readonly string[], delta: number): number {
  const safeDelta = assertFinite(delta, 'keyword delta');
  const lower = text.toLowerCase();
  return keywords.some((keyword) => lower.includes(keyword)) ? safeDelta : 0;
}

function tokenize(text: string): string[] {
  return text
    .split(TOKEN_SPLIT)
    .map((part) => part.trim().toLowerCase())
    .filter((part) => part.length > 0);
}

export function complexity(component: string, choice: string): DimensionScore {
  const tokens = tokenize(`${component} ${choice}`);
  const structural = Math.log2(tokens.length + 1);
  const keywordAdjust = keywordFactor(choice, ['managed', 'serverless', 'hosted'], MANAGED_COMPLEXITY_DELTA);
  const value = clampScore(COMPLEXITY_BASE + structural + keywordAdjust, 'complexity score');
  return {
    value,
    reason: `Complexity derives from ${tokens.length} concept tokens with managed adjustment ${keywordAdjust.toFixed(1)} → ${value.toFixed(2)}`,
  };
}

export function risk(component: string, choice: string): DimensionScore {
  let result = RISK_BASE;
  result += keywordFactor(choice, ['beta', 'experimental', 'preview'], RISK_BETA_PENALTY);
  result += keywordFactor(choice, ['legacy', 'replace', 'migration'], RISK_LEGACY_PENALTY);
  result += keywordFactor(choice, ['managed', 'hosted', 'proven'], RISK_MANAGED_BONUS);
  result += keywordFactor(component, ['network'], RISK_NETWORK_PENALTY);
  const value = clampScore(result, 'risk score');
  return {
    value,
    reason: `Risk adjusted by component '${component}' and keywords in '${choice}' → ${value.toFixed(2)}`,
  };
}

export function perf(component: string, choice: string): DimensionScore {
  let result = PERF_BASE;
  result += keywordFactor(choice, ['cache', 'accelerated', 'optimized'], PERF_ACCELERATED_BONUS);
  result += keywordFactor(choice, ['spot', 'cost'], PERF_COST_PENALTY);
  result += keywordFactor(component, ['compute'], PERF_COMPUTE_BONUS);
  result += keywordFactor(component, ['transfer'], PERF_TRANSFER_PENALTY);
  const value = clampScore(result, 'performance score');
  return {
    value,
    reason: `Performance baseline ${PERF_BASE} tuned by component '${component}' → ${value.toFixed(2)}`,
  };
}

export function devTime(component: string, choice: string): DimensionScore {
  const complexityScore = complexity(component, choice).value;
  const automationBonus = keywordFactor(choice, ['automated', 'managed', 'template'], AUTOMATION_BONUS);
  const value = clampScore(DEV_TIME_BASE + complexityScore / 2 + automationBonus, 'development time');
  return {
    value,
    reason: `Dev time proportional to complexity ${complexityScore.toFixed(2)} with automation bonus ${automationBonus.toFixed(1)} → ${value.toFixed(2)}`,
  };
}

export function depsReady(component: string, choice: string, repoSignals: RepoSignals = {}): DimensionScore {
  const readiness = (() => {
    const key = `${component}:${choice}`.toLowerCase();
    if (repoSignals[key] === 'ready') {
      return READINESS_READY;
    }
    if (repoSignals[key] === 'blocked') {
      return READINESS_BLOCKED;
    }
    const tokens = tokenize(choice);
    if (tokens.includes('existing') || tokens.includes('reuse')) {
      return READINESS_EXISTING;
    }
    if (tokens.includes('new') || tokens.includes('prototype')) {
      return READINESS_NEW;
    }
    return READINESS_DEFAULT;
  })();
  const value = clampScore(readiness, 'dependency readiness');
  return {
    value,
    reason: `Dependency readiness inferred from repo signals '${component}:${choice}' → ${value.toFixed(2)}`,
  };
}

export interface ScorePlanNodeInput extends ScoreContext {
  readonly overrides?: Partial<Record<Dimension, number>>;
}

function combineScores(scores: Record<Dimension, DimensionScore>, overrides: Partial<Record<Dimension, number>> = {}): Score {
  const explain: string[] = [];
  let weightedTotal = 0;

  (Object.keys(scores) as Dimension[]).forEach((dimension) => {
    const override = overrides[dimension];
    const value = override !== undefined ? clampScore(override, `${dimension} override`) : scores[dimension].value;
    weightedTotal += value * DIMENSION_WEIGHTS[dimension];
    const detail = override !== undefined
      ? `${dimension} overridden to ${value.toFixed(2)} (was ${scores[dimension].value.toFixed(2)})`
      : scores[dimension].reason;
    explain.push(detail);
  });

  const total = clampScore(weightedTotal, 'weighted total');
  explain.push(`Weighted total = ${total.toFixed(2)} using weights ${JSON.stringify(DIMENSION_WEIGHTS)}`);

  return {
    total,
    complexity: overrides.complexity ?? scores.complexity.value,
    risk: overrides.risk ?? scores.risk.value,
    perf: overrides.perf ?? scores.perf.value,
    devTime: overrides.devTime ?? scores.devTime.value,
    depsReady: overrides.depsReady ?? scores.depsReady.value,
    explain,
  };
}

export function scorePlanNode(input: ScorePlanNodeInput): Score {
  const baseScores: Record<Dimension, DimensionScore> = {
    complexity: complexity(input.component, input.choice),
    risk: risk(input.component, input.choice),
    perf: perf(input.component, input.choice),
    devTime: devTime(input.component, input.choice),
    depsReady: depsReady(input.component, input.choice, input.repoSignals),
  };

  const seeded = seedRng(`${input.component}|${input.choice}|${input.seed}`);
  const jitter = (dimension: Dimension, magnitude: number): number => {
    const offset = (seeded.next() - 0.5) * magnitude;
    return clampScore(baseScores[dimension].value + offset, `${dimension} jitter`);
  };

  const overrides: Partial<Record<Dimension, number>> = {
    perf: jitter('perf', 0.6),
    risk: jitter('risk', 0.4),
  };

  return combineScores(baseScores, overrides);
}
