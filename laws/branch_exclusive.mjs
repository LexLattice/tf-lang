import { proveGuardExclusive } from '../packages/prover/z3.mjs';

const POSITIVE_PATHS = new Set(['then', 'true', 'yes', 'allow', 'positive']);
const NEGATIVE_PATHS = new Set(['else', 'false', 'no', 'deny', 'negative']);

function describeValue(value) {
  if (typeof value === 'string') {
    return value;
  }
  if (typeof value === 'boolean') {
    return String(value);
  }
  if (value === null) {
    return 'null';
  }
  if (value === undefined) {
    return 'undefined';
  }
  try {
    return JSON.stringify(value);
  } catch (error) {
    return String(value);
  }
}

function stripOuterParens(text) {
  if (typeof text !== 'string') {
    return '';
  }
  let result = text.trim();
  while (result.startsWith('(') && result.endsWith(')')) {
    const inner = result.slice(1, -1).trim();
    if (inner.length === 0 || inner === result) {
      break;
    }
    result = inner;
  }
  return result;
}

function normalizeIdentifier(text) {
  if (typeof text !== 'string') {
    return '';
  }
  let candidate = stripOuterParens(text);
  let updated = true;
  while (updated) {
    updated = false;
    if (candidate.startsWith('@')) {
      candidate = candidate.slice(1).trim();
      updated = true;
      continue;
    }
    if (candidate.startsWith('¬')) {
      candidate = candidate.slice(1).trim();
      updated = true;
      continue;
    }
    if (candidate.startsWith('!')) {
      candidate = candidate.slice(1).trim();
      updated = true;
      continue;
    }
    if (/^not\b/i.test(candidate)) {
      candidate = candidate.replace(/^not\b/i, '').trim();
      updated = true;
    }
  }
  candidate = stripOuterParens(candidate).trim();
  return candidate;
}

function parseGuard(when) {
  const base = {
    kind: 'unknown',
    text: describeValue(when),
    normalized: null,
    var: null,
    negated: false,
    supported: false,
  };

  if (typeof when === 'boolean') {
    return {
      ...base,
      kind: 'const',
      text: String(when),
    };
  }

  if (typeof when === 'string') {
    const stripped = stripOuterParens(when);
    if (stripped.length === 0) {
      return base;
    }
    const lower = stripped.toLowerCase();
    if (lower === 'true' || lower === 'false') {
      return {
        ...base,
        kind: 'const',
        text: lower,
      };
    }

    let negated = false;
    let body = stripped;
    let updated = true;
    while (updated) {
      updated = false;
      const trimmed = body.trim();
      if (trimmed.startsWith('¬')) {
        negated = !negated;
        body = trimmed.slice(1);
        updated = true;
        continue;
      }
      if (trimmed.startsWith('!')) {
        negated = !negated;
        body = trimmed.slice(1);
        updated = true;
        continue;
      }
      if (/^not\b/i.test(trimmed)) {
        negated = !negated;
        body = trimmed.replace(/^not\b/i, '');
        updated = true;
        continue;
      }
    }
    body = stripOuterParens(body).trim();
    if (body.startsWith('@')) {
      body = body.slice(1);
    }
    const match = body.match(/^[A-Za-z0-9_.:]+/);
    if (match) {
      const variable = match[0];
      return {
        kind: 'var',
        text: negated ? `¬@${variable}` : `@${variable}`,
        normalized: `@${variable}`,
        var: variable,
        negated,
        supported: true,
      };
    }
    return base;
  }

  if (when && typeof when === 'object') {
    if (typeof when.op === 'string' && when.op.toLowerCase() === 'not' && typeof when.var === 'string') {
      const variable = normalizeIdentifier(when.var);
      if (variable) {
        return {
          kind: 'var',
          text: `¬@${variable}`,
          normalized: `@${variable}`,
          var: variable,
          negated: true,
          supported: true,
        };
      }
    }
    if (typeof when.var === 'string') {
      const variable = normalizeIdentifier(when.var);
      if (variable) {
        return {
          kind: 'var',
          text: `@${variable}`,
          normalized: `@${variable}`,
          var: variable,
          negated: false,
          supported: true,
        };
      }
    }
    return {
      ...base,
      kind: 'complex',
    };
  }

  return base;
}

function extractBranchMeta(node) {
  const meta = node && typeof node === 'object' ? node.metadata : null;
  if (!meta || typeof meta !== 'object') {
    return null;
  }
  const branch = meta.branch && typeof meta.branch === 'object' ? meta.branch : null;
  const candidates = [
    branch?.id,
    branch?.branch_id,
    branch?.name,
    branch?.group,
    meta.branch_id,
    meta.branchId,
  ];
  const id = candidates.find((value) => typeof value === 'string' && value.length > 0) ?? null;
  const pathCandidates = [branch?.path, branch?.side, branch?.role, meta.branch_path, meta.branchPath];
  const rawPath = pathCandidates.find((value) => typeof value === 'string' && value.length > 0) ?? null;
  return {
    id,
    path: rawPath,
  };
}

function normalizePath(path) {
  if (!path || typeof path !== 'string') {
    return null;
  }
  const normalized = path.trim().toLowerCase();
  if (POSITIVE_PATHS.has(normalized)) {
    return 'positive';
  }
  if (NEGATIVE_PATHS.has(normalized)) {
    return 'negative';
  }
  return null;
}

function determinePolarity(metaPath, guard) {
  const metaPolarity = normalizePath(metaPath);
  if (metaPolarity) {
    return metaPolarity;
  }
  if (guard.kind === 'var') {
    return guard.negated ? 'negative' : 'positive';
  }
  return 'unknown';
}

function createGroup(key, source) {
  return {
    key,
    source,
    positive: [],
    negative: [],
    neutral: [],
    guardVars: new Set(),
    hasMismatch: false,
  };
}

function buildGroups(nodes = []) {
  const groups = new Map();
  const fallback = new Map();

  for (const node of nodes) {
    if (!node || typeof node !== 'object') {
      continue;
    }
    const guard = parseGuard(node.when);
    const meta = extractBranchMeta(node);
    const targetKey = meta?.id;
    const metadataPolarity = normalizePath(meta?.path);
    const guardPolarity = guard.kind === 'var' ? (guard.negated ? 'negative' : 'positive') : null;
    const mismatch = Boolean(metadataPolarity && guardPolarity && metadataPolarity !== guardPolarity);

    const entry = {
      id: node.id ?? null,
      guard,
      path: meta?.path ?? null,
      metadataPolarity,
      guardPolarity,
      metadataGuardMismatch: mismatch,
    };

    if (guard.kind === 'var' && guard.var) {
      entry.guardVar = guard.var;
    }

    if (targetKey) {
      if (!groups.has(targetKey)) {
        groups.set(targetKey, createGroup(targetKey, 'metadata'));
      }
      const group = groups.get(targetKey);
      if (entry.guardVar) {
        group.guardVars.add(entry.guardVar);
      }
      const polarity = determinePolarity(meta?.path, guard);
      if (mismatch) {
        group.hasMismatch = true;
      }
      if (polarity === 'positive') {
        group.positive.push(entry);
      } else if (polarity === 'negative') {
        group.negative.push(entry);
      } else {
        group.neutral.push(entry);
      }
      continue;
    }

    if (guard.kind === 'var' && guard.var) {
      if (!fallback.has(guard.var)) {
        fallback.set(guard.var, createGroup(guard.var, 'guard'));
      }
      const group = fallback.get(guard.var);
      group.guardVars.add(guard.var);
      if (guard.negated) {
        group.negative.push(entry);
      } else {
        group.positive.push(entry);
      }
    }
  }

  const output = [...groups.values()];
  for (const group of fallback.values()) {
    if (group.positive.length > 0 && group.negative.length > 0) {
      output.push(group);
    }
  }
  return output;
}

function formatEntry(entry) {
  return {
    id: entry.id,
    path: entry.path ?? null,
    guard: {
      kind: entry.guard.kind,
      text: entry.guard.text,
      normalized: entry.guard.normalized ?? null,
      var: entry.guard.var,
      negated: Boolean(entry.guard.negated),
      supported: Boolean(entry.guard.supported),
    },
    metadataPolarity: entry.metadataPolarity ?? null,
    guardPolarity: entry.guardPolarity ?? null,
    metadataGuardMismatch: Boolean(entry.metadataGuardMismatch),
  };
}

export async function checkBranchExclusive({ nodes = [] } = {}) {
  const groups = buildGroups(nodes).sort((a, b) => {
    const aKey = `${a.source}:${a.key ?? ''}`;
    const bKey = `${b.source}:${b.key ?? ''}`;
    if (aKey < bKey) return -1;
    if (aKey > bKey) return 1;
    return 0;
  });
  const results = [];

  for (const group of groups) {
    if (group.positive.length === 0 && group.negative.length === 0) {
      continue;
    }

    const result = {
      branch: group.source === 'metadata' ? group.key : null,
      guardVar: group.guardVars.size === 1 ? [...group.guardVars][0] : null,
      source: group.source,
      positive: group.positive.map(formatEntry),
      negative: group.negative.map(formatEntry),
      neutral: group.neutral.map(formatEntry),
      status: 'NEUTRAL',
      reason: null,
      proved: null,
      guard: null,
      ok: true,
      warnings: [],
    };

    const warnings = new Set();

    if (group.guardVars.size > 1) {
      warnings.add('mixed-guard-vars');
    }
    if (group.hasMismatch) {
      warnings.add('metadata-guard-mismatch');
    }

    if (group.positive.length === 0 || group.negative.length === 0) {
      result.status = 'WARN';
      result.reason = group.positive.length === 0 ? 'missing-positive' : 'missing-negative';
      result.ok = true;
      results.push(result);
      continue;
    }

    const positiveGuard = group.positive.map((entry) => entry.guard).find((guard) => guard.supported);
    const negativeGuard = group.negative.map((entry) => entry.guard).find((guard) => guard.supported);

    if (!positiveGuard || !negativeGuard) {
      result.status = 'WARN';
      result.reason = 'unsupported-guard';
      result.ok = true;
      results.push(result);
      continue;
    }

    if (!result.guardVar) {
      if (positiveGuard.var && negativeGuard.var && positiveGuard.var === negativeGuard.var) {
        result.guardVar = positiveGuard.var;
      } else {
        result.guardVar = positiveGuard.var ?? negativeGuard.var ?? null;
      }
    }

    result.guard = positiveGuard.normalized
      ?? negativeGuard.normalized
      ?? (result.guardVar ? `@${result.guardVar}` : null);

    const selectWarningReason = () => {
      if (warnings.has('metadata-guard-mismatch')) return 'metadata-guard-mismatch';
      if (warnings.has('mixed-guard-vars')) return 'mixed-guard-vars';
      return null;
    };

    try {
      const proved = await proveGuardExclusive({
        guardVar: result.guardVar,
        positiveNegated: Boolean(positiveGuard.negated),
        negativeNegated: Boolean(negativeGuard.negated),
      });
      result.proved = proved;
      if (proved) {
        const warningReason = selectWarningReason();
        if (warningReason) {
          result.status = 'WARN';
          result.reason = warningReason;
        } else {
          result.status = 'PASS';
          result.reason = null;
        }
      } else {
        result.status = 'ERROR';
        result.reason = 'overlap';
      }
    } catch (error) {
      result.status = 'ERROR';
      result.reason = 'solver-failed';
      result.error = error?.message ?? 'solver-failed';
    }

    result.warnings = [...warnings];
    result.ok = result.status !== 'ERROR';

    results.push(result);
  }

  const ok = results.every((entry) => entry.ok);
  return { ok, results };
}

export default checkBranchExclusive;
