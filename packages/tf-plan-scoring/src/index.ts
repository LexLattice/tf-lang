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

function clampScore(value: number): number {
  if (Number.isNaN(value)) {
    return 0;
  }
  return Math.min(10, Math.max(0, Number.parseFloat(value.toFixed(3))));
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
  perf: 0.35,
  depsReady: 0.2,
  complexity: 0.15,
  devTime: 0.15,
  risk: 0.15,
};

const defaultComplexityBase = 4.5;

export function complexity(component: string, choice: string): DimensionScore {
  const tokens = tokenize(`${component} ${choice}`);
  const structural = Math.log2(tokens.length + 1);
  const keywordAdjust = keywordFactor(choice, ['managed', 'serverless', 'hosted'], -1.2);
  const value = clampScore(defaultComplexityBase + structural + keywordAdjust);
  return {
    value,
    reason: `Complexity derives from ${tokens.length} concept tokens with managed adjustment ${keywordAdjust.toFixed(1)} → ${value.toFixed(2)}`,
  };
}

export function risk(component: string, choice: string): DimensionScore {
  const base = 3.5;
  let result = base;
  result += keywordFactor(choice, ['beta', 'experimental', 'preview'], 3.2);
  result += keywordFactor(choice, ['legacy', 'replace', 'migration'], 2.1);
  result += keywordFactor(choice, ['managed', 'hosted', 'proven'], -1.3);
  result += keywordFactor(component, ['network'], 0.4);
  const value = clampScore(result);
  return {
    value,
    reason: `Risk adjusted by component '${component}' and keywords in '${choice}' → ${value.toFixed(2)}`,
  };
}

export function perf(component: string, choice: string): DimensionScore {
  const base = 6;
  let result = base;
  result += keywordFactor(choice, ['cache', 'accelerated', 'optimized'], 1.8);
  result += keywordFactor(choice, ['spot', 'cost'], -1.5);
  result += keywordFactor(component, ['compute'], 0.6);
  result += keywordFactor(component, ['transfer'], -0.3);
  const value = clampScore(result);
  return {
    value,
    reason: `Performance baseline ${base} tuned by component '${component}' → ${value.toFixed(2)}`,
  };
}

export function devTime(component: string, choice: string): DimensionScore {
  const complexityScore = complexity(component, choice).value;
  const automationBonus = keywordFactor(choice, ['automated', 'managed', 'template'], -1.0);
  const value = clampScore(5 + complexityScore / 2 + automationBonus);
  return {
    value,
    reason: `Dev time proportional to complexity ${complexityScore.toFixed(2)} with automation bonus ${automationBonus.toFixed(1)} → ${value.toFixed(2)}`,
  };
}

export function depsReady(component: string, choice: string, repoSignals: RepoSignals = {}): DimensionScore {
  const readiness = (() => {
    const key = `${component}:${choice}`.toLowerCase();
    if (repoSignals[key] === 'ready') {
      return 9.5;
    }
    if (repoSignals[key] === 'blocked') {
      return 2.5;
    }
    const tokens = tokenize(choice);
    if (tokens.includes('existing') || tokens.includes('reuse')) {
      return 8.5;
    }
    if (tokens.includes('new') || tokens.includes('prototype')) {
      return 4.5;
    }
    return 6.5;
  })();
  const value = clampScore(readiness);
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
    const value = override !== undefined ? clampScore(override) : scores[dimension].value;
    weightedTotal += value * dimensionWeights[dimension];
    const detail = override !== undefined
      ? `${dimension} overridden to ${value.toFixed(2)} (was ${scores[dimension].value.toFixed(2)})`
      : scores[dimension].reason;
    explain.push(detail);
  });

  const total = clampScore(weightedTotal);
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
    return clampScore(baseScores[dimension].value + offset);
  };

  const overrides: Partial<Record<Dimension, number>> = {
    perf: jitter('perf', 0.6),
    risk: jitter('risk', 0.4),
  };

  return combineScores(baseScores, overrides);
}
