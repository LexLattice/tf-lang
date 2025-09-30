import fs from "fs";
import yaml from "yaml";

export function loadRulebookPlan(rulebookPath) {
  const rb = yaml.parse(fs.readFileSync(rulebookPath, "utf8"));
  return normalizeRulebook(rb || {});
}

export function rulesForPhase(rulebookPath, phaseId) {
  const plan = loadRulebookPlan(rulebookPath);
  return rulesForPhaseFromPlan(plan, phaseId);
}

export function rulesForPhaseFromPlan(plan, phaseId) {
  const phase = plan.phases.get(phaseId);
  if (!phase) {
    throw new Error(`unknown phase "${phaseId}"`);
  }
  return phase.rules.map((rule) => ({ ...rule }));
}

function normalizeRulebook(rb) {
  const phases = toPhaseRecords(rb?.phases);
  const ruleMap = toRuleMap(rb?.rules);

  const expandedPhases = new Map();
  const cache = new Map();
  const stack = [];

  const expandPhase = (phaseId) => {
    if (cache.has(phaseId)) {
      return cache.get(phaseId);
    }

    const phase = phases.get(phaseId);
    if (!phase) {
      throw new Error(`unknown phase "${phaseId}"`);
    }

    if (stack.includes(phaseId)) {
      const start = stack.indexOf(phaseId);
      const cycle = [...stack.slice(start), phaseId];
      throw new Error(`cycle detected via "${cycle.join(" -> ")}"`);
    }

    stack.push(phaseId);
    const seen = new Set();
    const ordered = [];

    for (const inherited of phase.inherits) {
      if (!phases.has(inherited)) {
        throw new Error(`invalid inherits reference "${inherited}"`);
      }
      const inheritedRules = expandPhase(inherited);
      for (const rule of inheritedRules) {
        if (seen.has(rule.id)) continue;
        seen.add(rule.id);
        ordered.push(rule);
      }
    }

    for (const entry of phase.ruleEntries) {
      const normalized = resolveRuleEntry(entry, ruleMap);
      if (seen.has(normalized.id)) continue;
      seen.add(normalized.id);
      ordered.push(normalized);
    }

    stack.pop();
    const finalized = ordered.map((rule) => ({ ...rule }));
    cache.set(phaseId, finalized);
    return finalized;
  };

  for (const [id, phase] of phases.entries()) {
    const rules = expandPhase(id).map((rule) => ({ ...rule }));
    expandedPhases.set(id, {
      id,
      inherits: [...phase.inherits],
      rules,
      ...phase.meta,
    });
  }

  return { phases: expandedPhases, ruleMap };
}

function toPhaseRecords(phasesNode) {
  const phases = new Map();

  if (Array.isArray(phasesNode)) {
    for (const [index, value] of phasesNode.entries()) {
      if (!value || typeof value !== "object" || Array.isArray(value)) {
        throw new Error(`phase entry at index ${index} must be an object`);
      }
      if (typeof value.id !== "string" || value.id.length === 0) {
        throw new Error(`phase entry at index ${index} is missing an id`);
      }
      if (phases.has(value.id)) {
        throw new Error(`duplicate phase "${value.id}"`);
      }
      const record = buildPhaseRecord(value.id, value);
      phases.set(value.id, record);
    }
    return phases;
  }

  if (phasesNode && typeof phasesNode === "object") {
    for (const [id, value] of Object.entries(phasesNode)) {
      if (!value || typeof value !== "object" || Array.isArray(value)) {
        throw new Error(`phase "${id}" must be an object`);
      }
      if (phases.has(id)) {
        throw new Error(`duplicate phase "${id}"`);
      }
      const record = buildPhaseRecord(id, value);
      phases.set(id, record);
    }
    return phases;
  }

  throw new Error("rulebook phases must be an array or object");
}

function buildPhaseRecord(id, value) {
  const inherits = normalizeInherits(value.inherits, id);
  const ruleEntries = normalizePhaseRules(value.rules, id);
  const meta = collectMeta(value);
  return { id, inherits, ruleEntries, meta };
}

function collectMeta(value) {
  const meta = {};
  for (const [key, val] of Object.entries(value)) {
    if (key === "id" || key === "inherits" || key === "rules") continue;
    meta[key] = val;
  }
  return meta;
}

function toRuleMap(rulesNode) {
  const map = new Map();
  if (rulesNode === undefined || rulesNode === null) {
    return map;
  }

  if (Array.isArray(rulesNode)) {
    for (const [index, entry] of rulesNode.entries()) {
      if (!entry || typeof entry !== "object" || Array.isArray(entry)) {
        throw new Error(`rule definition at index ${index} must be an object`);
      }
      if (typeof entry.id !== "string" || entry.id.length === 0) {
        throw new Error(`rule definition at index ${index} is missing an id`);
      }
      if (!map.has(entry.id)) {
        map.set(entry.id, { ...entry });
      }
    }
    return map;
  }

  if (typeof rulesNode === "object") {
    for (const [id, definition] of Object.entries(rulesNode)) {
      if (!definition || typeof definition !== "object" || Array.isArray(definition)) {
        continue;
      }
      if (!map.has(id)) {
        map.set(id, { id, ...definition });
      }
    }
    return map;
  }

  throw new Error("rule definitions must be an array or object");
}

function normalizeInherits(value, phaseId) {
  if (value === undefined) return [];
  if (!Array.isArray(value)) {
    throw new Error(`inherits for phase "${phaseId}" must be an array`);
  }
  return value.map((entry, index) => {
    if (typeof entry !== "string" || entry.length === 0) {
      throw new Error(
        `inherits for phase "${phaseId}" must contain only phase ids (invalid entry at index ${index})`,
      );
    }
    return entry;
  });
}

function normalizePhaseRules(value, phaseId) {
  if (value === undefined) return [];

  if (Array.isArray(value)) {
    return value.map((entry) => normalizeRuleReference(entry, phaseId));
  }

  if (value && typeof value === "object") {
    return Object.entries(value).map(([id, config]) => {
      const entry =
        config && typeof config === "object" && !Array.isArray(config)
          ? { id, ...config }
          : { id };
      return normalizeRuleReference(entry, phaseId);
    });
  }

  throw new Error(`invalid rule entry at phase "${phaseId}"`);
}

function normalizeRuleReference(entry, phaseId) {
  if (typeof entry === "string") {
    return entry;
  }

  if (entry && typeof entry === "object" && !Array.isArray(entry)) {
    if (typeof entry.id !== "string" || entry.id.length === 0) {
      throw new Error(`invalid rule entry at phase "${phaseId}"`);
    }
    return { ...entry, id: entry.id };
  }

  throw new Error(`invalid rule entry at phase "${phaseId}"`);
}

function resolveRuleEntry(entry, ruleMap) {
  if (typeof entry === "string") {
    const rule = ruleMap.get(entry);
    if (!rule) {
      throw new Error(`unknown rule "${entry}"`);
    }
    return { ...rule };
  }

  const fallback = ruleMap.get(entry.id) || {};
  return { ...fallback, ...entry, id: entry.id };
}
