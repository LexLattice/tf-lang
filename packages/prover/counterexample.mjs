function normalizeVariables(input) {
  if (!Array.isArray(input)) {
    return [];
  }
  const seen = new Set();
  const vars = [];
  for (const name of input) {
    if (typeof name !== 'string') {
      continue;
    }
    const trimmed = name.trim();
    if (!trimmed || seen.has(trimmed)) {
      continue;
    }
    seen.add(trimmed);
    vars.push(trimmed);
  }
  return vars.sort((a, b) => (a < b ? -1 : a > b ? 1 : 0));
}

function collectTriggered(entries = [], assignment = {}) {
  const triggered = [];
  for (const entry of entries) {
    const guard = entry?.guard;
    if (!guard || guard.kind !== 'var' || typeof guard.var !== 'string') {
      continue;
    }
    const value = Boolean(assignment[guard.var]);
    const active = guard.negated ? !value : value;
    if (active) {
      if (typeof entry.id === 'string') {
        triggered.push(entry.id);
      } else if (entry.id !== null && entry.id !== undefined) {
        triggered.push(String(entry.id));
      }
    }
  }
  return triggered.sort((a, b) => (a < b ? -1 : a > b ? 1 : 0));
}

function makePayload({
  goal,
  guard,
  reason,
  assignment,
  positive,
  negative,
}) {
  const hasAssignment = assignment && typeof assignment === 'object';
  const normalizedAssignment = hasAssignment ? assignment : {};
  const triggered = hasAssignment
    ? {
        positive: collectTriggered(positive, normalizedAssignment),
        negative: collectTriggered(negative, normalizedAssignment),
      }
    : { positive: [], negative: [] };

  const payload = {
    goal: goal ?? 'branch-exclusive',
    guard: guard ?? null,
    reason,
    assignment: normalizedAssignment,
    triggered,
  };
  return payload;
}

export function findCounterexample({
  goal = 'branch-exclusive',
  guard = null,
  reason = 'overlap',
  variables = [],
  predicate,
  positive = [],
  negative = [],
  maxBools = 8,
} = {}) {
  const uniqueVars = normalizeVariables(variables);
  const sanitizedMax = Number.isInteger(maxBools) ? maxBools : 8;
  const cappedMax = Math.min(Math.max(sanitizedMax, 1), 8);

  if (sanitizedMax > 8 || uniqueVars.length > cappedMax) {
    return makePayload({
      goal,
      guard: guard ?? (uniqueVars.length === 1 ? `@${uniqueVars[0]}` : guard),
      reason: 'max-bools-exceeded',
      assignment: null,
      positive,
      negative,
    });
  }

  if (uniqueVars.length === 0) {
    return null;
  }

  if (reason !== 'overlap') {
    return makePayload({ goal, guard, reason, assignment: null, positive, negative });
  }

  if (typeof predicate !== 'function') {
    throw new Error('predicate-required');
  }

  const total = 1 << uniqueVars.length;
  for (let mask = 0; mask < total; mask += 1) {
    const assignment = {};
    for (let index = 0; index < uniqueVars.length; index += 1) {
      assignment[uniqueVars[index]] = Boolean((mask >> index) & 1);
    }
    const holds = Boolean(predicate(assignment));
    if (!holds) {
      return makePayload({ goal, guard, reason: 'overlap', assignment, positive, negative });
    }
  }
  return null;
}

export default {
  findCounterexample,
};
