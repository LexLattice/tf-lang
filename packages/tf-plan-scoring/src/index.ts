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

const PERF_WEIGHT = 0.35;
const DEPS_READY_WEIGHT = 0.2;
const COMPLEXITY_WEIGHT = 0.15;
const DEV_TIME_WEIGHT = 0.15;
const RISK_WEIGHT = 0.15;

const COMPLEXITY_BASE = 4.5;
const MANAGED_COMPLEXITY_DELTA = -1.2;
const RISK_BASE = 3.5;
const RISK_BETA_DELTA = 3.2;
const RISK_LEGACY_DELTA = 2.1;
const RISK_PROVEN_DELTA = -1.3;
const RISK_NETWORK_DELTA = 0.4;
const PERF_BASE = 6;
const PERF_ACCELERATION_BONUS = 1.8;
const PERF_COST_PENALTY = -1.5;
const PERF_COMPUTE_BONUS = 0.6;
const PERF_TRANSFER_PENALTY = -0.3;
const DEV_TIME_BASE = 5;
const AUTOMATION_BONUS = -1.0;
const READINESS_READY_SCORE = 9.5;
const READINESS_BLOCKED_SCORE = 2.5;
const READINESS_EXISTING_SCORE = 8.5;
const READINESS_NEW_SCORE = 4.5;
const READINESS_DEFAULT_SCORE = 6.5;
const PERF_JITTER_MAGNITUDE = 0.6;
const RISK_JITTER_MAGNITUDE = 0.4;

function assertFinite(value: number, context: string): number {
  if (!Number.isFinite(value)) {
    throw new Error(`Non-finite value for ${context}: ${value}`);
  }
  return value;
}

function clampScore(value: number, context: string): number {
  const finite = assertFinite(value, context);
  return Math.min(10, Math.max(0, Number.parseFloat(finite.toFixed(3))));
}

function keywordFactor(text: string, keywords: readonly string[], delta: number): number {
  const lower = text.toLowerCase();
  for (const keyword of keywords) {
    if (lower.includes(keyword)) {
      return delta;
    }
  }
  return 0;
}

function tokenize(text: string): string[] {
  return text
    .split(/[^a-z0-9]+/i)
    .map((part) => part.trim().toLowerCase())
    .filter((part) => part.length > 0);
}

const dimensionWeights: Record<Dimension, number> = {
  perf: PERF_WEIGHT,
  depsReady: DEPS_READY_WEIGHT,
  complexity: COMPLEXITY_WEIGHT,
  devTime: DEV_TIME_WEIGHT,
  risk: RISK_WEIGHT,
};

export function complexity(component: string, choice: string): DimensionScore {
  const tokens = tokenize(`${component} ${choice}`);
  const structural = Math.log2(tokens.length + 1);
  const keywordAdjust = keywordFactor(choice, ['managed', 'serverless', 'hosted'], MANAGED_COMPLEXITY_DELTA);
  const value = clampScore(COMPLEXITY_BASE + structural + keywordAdjust, 'complexity');
  return {
    value,
    reason: `Complexity derives from ${tokens.length} concept tokens with managed adjustment ${keywordAdjust.toFixed(1)} → ${value.toFixed(2)}`,
  };
}

export function risk(component: string, choice: string): DimensionScore {
  let result = RISK_BASE;
  result += keywordFactor(choice, ['beta', 'experimental', 'preview'], RISK_BETA_DELTA);
  result += keywordFactor(choice, ['legacy', 'replace', 'migration'], RISK_LEGACY_DELTA);
  result += keywordFactor(choice, ['managed', 'hosted', 'proven'], RISK_PROVEN_DELTA);
  result += keywordFactor(component, ['network'], RISK_NETWORK_DELTA);
  const value = clampScore(result, 'risk');
  return {
    value,
    reason: `Risk adjusted by component '${component}' and keywords in '${choice}' → ${value.toFixed(2)}`,
  };
}

export function perf(component: string, choice: string): DimensionScore {
  let result = PERF_BASE;
  result += keywordFactor(choice, ['cache', 'accelerated', 'optimized'], PERF_ACCELERATION_BONUS);
  result += keywordFactor(choice, ['spot', 'cost'], PERF_COST_PENALTY);
  result += keywordFactor(component, ['compute'], PERF_COMPUTE_BONUS);
  result += keywordFactor(component, ['transfer'], PERF_TRANSFER_PENALTY);
  const value = clampScore(result, 'performance');
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
      return READINESS_READY_SCORE;
    }
    if (repoSignals[key] === 'blocked') {
      return READINESS_BLOCKED_SCORE;
    }
    const tokens = tokenize(choice);
    if (tokens.includes('existing') || tokens.includes('reuse')) {
      return READINESS_EXISTING_SCORE;
    }
    if (tokens.includes('new') || tokens.includes('prototype')) {
      return READINESS_NEW_SCORE;
    }
    return READINESS_DEFAULT_SCORE;
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
    weightedTotal += value * dimensionWeights[dimension];
    const detail = override !== undefined
      ? `${dimension} overridden to ${value.toFixed(2)} (was ${scores[dimension].value.toFixed(2)})`
      : scores[dimension].reason;
    explain.push(detail);
  });

  const total = clampScore(weightedTotal, 'weighted total');
  explain.push(`Weighted total = ${total.toFixed(2)} using weights ${JSON.stringify(dimensionWeights)}`);

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
    perf: jitter('perf', PERF_JITTER_MAGNITUDE),
    risk: jitter('risk', RISK_JITTER_MAGNITUDE),
  };

  return combineScores(baseScores, overrides);
}
