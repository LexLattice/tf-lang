import { createScore, Score } from '@tf-lang/tf-plan-core';

export interface RepoSignals {
  readonly componentMaturity?: Record<string, number>;
  readonly dependencyHealth?: Record<string, number>;
}

export interface ScoreInput {
  readonly component: string;
  readonly choice: string;
  readonly repoSignals?: RepoSignals;
}

function normalizeName(name: string): string {
  return name.toLowerCase();
}

export function complexity(component: string, choice: string): { value: number; reason: string } {
  const base = Math.max(1, Math.ceil(choice.length / 8));
  const componentFactor = normalizeName(component).includes('network') ? 2 : 1;
  const value = base * componentFactor;
  const reason = `Complexity scaled by choice length (${choice.length}) and component type`;
  return { value, reason };
}

export function risk(component: string, choice: string, repoSignals?: RepoSignals): { value: number; reason: string } {
  const normalized = normalizeName(choice);
  let value = normalized.includes('beta') ? 4 : 2;
  if (repoSignals?.componentMaturity) {
    const maturity = repoSignals.componentMaturity[normalizeName(component)] ?? 0;
    value = Math.max(1, value - Math.round(maturity));
  }
  const reason = `Risk adjusted for maturity signals (component=${component})`;
  return { value, reason };
}

export function perf(component: string, choice: string): { value: number; reason: string } {
  const normalized = normalizeName(choice);
  let value = 5;
  if (normalized.includes('small') || normalized.includes('micro')) {
    value = 3;
  } else if (normalized.includes('large')) {
    value = 7;
  }
  const reason = `Performance inferred from choice keywords (${choice})`;
  return { value, reason };
}

export function devTime(component: string, choice: string): { value: number; reason: string } {
  const complexityScore = complexity(component, choice).value;
  const value = Math.max(1, Math.round(complexityScore * 1.5));
  const reason = `Development time derived from complexity (${complexityScore})`;
  return { value, reason };
}

export function depsReady(
  component: string,
  choice: string,
  repoSignals?: RepoSignals,
): { value: number; reason: string } {
  const normalizedComponent = normalizeName(component);
  const health = repoSignals?.dependencyHealth?.[normalizedComponent];
  const value = typeof health === 'number' ? Math.max(0, Math.min(10, health)) : 5;
  const reason = `Dependency readiness ${(health ?? 5).toFixed(2)} for ${component}`;
  return { value, reason };
}

export interface ScorePlanNodeInput extends ScoreInput {}

export function scorePlanNode(input: ScorePlanNodeInput): Score {
  const complexityResult = complexity(input.component, input.choice);
  const riskResult = risk(input.component, input.choice, input.repoSignals);
  const perfResult = perf(input.component, input.choice);
  const devTimeResult = devTime(input.component, input.choice);
  const depsReadyResult = depsReady(input.component, input.choice, input.repoSignals);

  return createScore({
    complexity: complexityResult.value,
    risk: riskResult.value,
    perf: perfResult.value,
    devTime: devTimeResult.value,
    depsReady: depsReadyResult.value,
    explain: [
      complexityResult.reason,
      riskResult.reason,
      perfResult.reason,
      devTimeResult.reason,
      depsReadyResult.reason,
    ],
  });
}
