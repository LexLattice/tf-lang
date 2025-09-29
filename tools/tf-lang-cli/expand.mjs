import fs from "fs";
import yaml from "yaml";

export function rulesForPhase(rulebookPath, phaseId) {
  const rb = yaml.parse(fs.readFileSync(rulebookPath, "utf8"));
  const { phases, ruleMap } = normalizeRulebook(rb);
  const seen = new Set();
  const ordered = [];

  function addPhase(pid) {
    const phase = phases.get(pid);
    if (!phase) {
      throw new Error(`unknown phase ${pid}`);
    }
    for (const inherited of phase.inherits || []) {
      addPhase(inherited);
    }
    for (const entry of phase.rules || []) {
      const normalized = normalizeRuleEntry(entry, ruleMap);
      if (!normalized) continue;
      if (seen.has(normalized.id)) continue;
      seen.add(normalized.id);
      ordered.push(normalized);
    }
  }

  addPhase(phaseId);
  return ordered;
}

function normalizeRulebook(rb) {
  const phases = new Map();

  // phases may be an array of objects { id, inherits, rules } or a mapping { id: {...} }
  if (Array.isArray(rb?.phases)) {
    for (const item of rb.phases) {
      if (!item || typeof item !== "object") continue;
      if (typeof item.id !== "string" || item.id.length === 0) continue;
      phases.set(item.id, {
        ...item,
        inherits: Array.isArray(item.inherits) ? item.inherits : [],
        rules: Array.isArray(item.rules) ? item.rules : [],
      });
    }
  } else if (rb && typeof rb.phases === "object") {
    for (const [id, value] of Object.entries(rb.phases)) {
      if (!value || typeof value !== "object") continue;
      phases.set(id, {
        id,
        ...value,
        inherits: Array.isArray(value.inherits) ? value.inherits : [],
        rules: Array.isArray(value.rules) ? value.rules : [],
      });
    }
  }

  const ruleMap = new Map();
  if (rb && typeof rb.rules === "object") {
    for (const [id, definition] of Object.entries(rb.rules)) {
      if (!definition || typeof definition !== "object") continue;
      ruleMap.set(id, { id, ...definition });
    }
  }

  return { phases, ruleMap };
}

function normalizeRuleEntry(entry, ruleMap) {
  if (!entry) return null;

  // string id -> look up in ruleMap
  if (typeof entry === "string") {
    const rule = ruleMap.get(entry);
    if (!rule) throw new Error(`unknown rule ${entry}`);
    return rule;
  }

  // object { id, ... } -> merge with ruleMap fallback
  if (typeof entry === "object") {
    const id = typeof entry.id === "string" ? entry.id : null;
    if (!id) throw new Error("rule entry missing id");
    const normalized = { ...entry };
    if (!normalized.kind && ruleMap.has(id)) {
      const fallback = ruleMap.get(id);
      return { ...fallback, ...normalized };
    }
    return normalized;
  }

  return null;
}
