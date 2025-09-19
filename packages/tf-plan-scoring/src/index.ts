import {
  RepoSignals,
  Score,
  seedRng,
} from '@tf-lang/tf-plan-core';

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

const SCORE_MIN = 0;
const SCORE_MAX = 10;
const SCORE_PRECISION = 3;

const DIMENSION_WEIGHTS: Record<Dimension, number> = {
  perf: 0.35,
  depsReady: 0.2,
  complexity: 0.15,
  devTime: 0.15,
  risk: 0.15,
};

const COMPLEXITY_BASELINE = 4.5; // Base complexity before keyword adjustments.
const COMPLEXITY_MANAGED_ADJUST = -1.2;

const RISK_BASELINE = 3.5; // Default risk without modifiers.
const RISK_BETA_PENALTY = 3.2;
const RISK_MIGRATION_PENALTY = 2.1;
const RISK_MANAGED_REDUCTION = -1.3;
const RISK_NETWORK_INCREMENT = 0.4;

const PERF_BASELINE = 6; // Balanced throughput starting point.
const PERF_ACCELERATION_BONUS = 1.8;
const PERF_COST_TRADEOFF = -1.5;
const PERF_COMPUTE_BONUS = 0.6;
const PERF_TRANSFER_PENALTY = -0.3;

const DEV_TIME_BASELINE = 5; // Average iteration time.
const DEV_TIME_AUTOMATION_BONUS = -1.0;

const PERF_JITTER_MAGNITUDE = 0.6;
const RISK_JITTER_MAGNITUDE = 0.4;

const REPO_READY_SCORE = 9.5;
const REPO_BLOCKED_SCORE = 2.5;
const REPO_EXISTING_BONUS = 8.5;
const REPO_PROTOTYPE_PENALTY = 4.5;
const REPO_DEFAULT_SCORE = 6.5;

function clamp01(value: number, label: string): number {
  if (!Number.isFinite(value)) {
    throw new Error(`Score for ${label} resolved to non-finite value: ${value}`);
  }
  return Math.min(SCORE_MAX, Math.max(SCORE_MIN, Number.parseFloat(value.toFixed(SCORE_PRECISION))));
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

export function complexity(component: string, choice: string): DimensionScore {
  const tokens = tokenize(`${component} ${choice}`);
  const structural = Math.log2(tokens.length + 1);
  const keywordAdjust = keywordFactor(choice, ['managed', 'serverless', 'hosted'], COMPLEXITY_MANAGED_ADJUST);
  const value = clamp01(
    COMPLEXITY_BASELINE + structural + keywordAdjust,
    `complexity(${component},${choice})`,
  );
  return {
    value,
    reason: `Complexity derives from ${tokens.length} concept tokens with managed adjustment ${keywordAdjust.toFixed(1)} → ${value.toFixed(2)}`,
  };
}

export function risk(component: string, choice: string): DimensionScore {
  let result = RISK_BASELINE;
  result += keywordFactor(choice, ['beta', 'experimental', 'preview'], RISK_BETA_PENALTY);
  result += keywordFactor(choice, ['legacy', 'replace', 'migration'], RISK_MIGRATION_PENALTY);
  result += keywordFactor(choice, ['managed', 'hosted', 'proven'], RISK_MANAGED_REDUCTION);
  result += keywordFactor(component, ['network'], RISK_NETWORK_INCREMENT);
  const value = clamp01(result, `risk(${component},${choice})`);
  return {
    value,
    reason: `Risk adjusted by component '${component}' and keywords in '${choice}' → ${value.toFixed(2)}`,
  };
}

export function perf(component: string, choice: string): DimensionScore {
  let result = PERF_BASELINE;
  result += keywordFactor(choice, ['cache', 'accelerated', 'optimized'], PERF_ACCELERATION_BONUS);
  result += keywordFactor(choice, ['spot', 'cost'], PERF_COST_TRADEOFF);
  result += keywordFactor(component, ['compute'], PERF_COMPUTE_BONUS);
  result += keywordFactor(component, ['transfer'], PERF_TRANSFER_PENALTY);
  const value = clamp01(result, `perf(${component},${choice})`);
  return {
    value,
    reason: `Performance baseline ${PERF_BASELINE} tuned by component '${component}' → ${value.toFixed(2)}`,
  };
}

export function devTime(component: string, choice: string): DimensionScore {
  const complexityScore = complexity(component, choice).value;
  const automationBonus = keywordFactor(choice, ['automated', 'managed', 'template'], DEV_TIME_AUTOMATION_BONUS);
  const value = clamp01(
    DEV_TIME_BASELINE + complexityScore / 2 + automationBonus,
    `devTime(${component},${choice})`,
  );
  return {
    value,
    reason: `Dev time proportional to complexity ${complexityScore.toFixed(2)} with automation bonus ${automationBonus.toFixed(1)} → ${value.toFixed(2)}`,
  };
}

export function depsReady(component: string, choice: string, repoSignals: RepoSignals = {}): DimensionScore {
  const readiness = (() => {
    const key = `${component}:${choice}`.toLowerCase();
    if (repoSignals[key] === 'ready') {
      return REPO_READY_SCORE;
    }
    if (repoSignals[key] === 'blocked') {
      return REPO_BLOCKED_SCORE;
    }
    const tokens = tokenize(choice);
    if (tokens.includes('existing') || tokens.includes('reuse')) {
      return REPO_EXISTING_BONUS;
    }
    if (tokens.includes('new') || tokens.includes('prototype')) {
      return REPO_PROTOTYPE_PENALTY;
    }
    return REPO_DEFAULT_SCORE;
  })();
  const value = clamp01(readiness, `depsReady(${component},${choice})`);
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
    const value = override !== undefined ? clamp01(override, `${dimension} override`) : scores[dimension].value;
    weightedTotal += value * DIMENSION_WEIGHTS[dimension];
    const detail = override !== undefined
      ? `${dimension} overridden to ${value.toFixed(2)} (was ${scores[dimension].value.toFixed(2)})`
      : scores[dimension].reason;
    explain.push(detail);
  });

  const total = clamp01(weightedTotal, 'total');
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
    return clamp01(baseScores[dimension].value + offset, `${dimension} jitter`);
  };

  const overrides: Partial<Record<Dimension, number>> = {
    perf: jitter('perf', PERF_JITTER_MAGNITUDE),
    risk: jitter('risk', RISK_JITTER_MAGNITUDE),
  };

  return combineScores(baseScores, overrides);
}
