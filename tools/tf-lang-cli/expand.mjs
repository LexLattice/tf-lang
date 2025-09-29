import fs from "fs"; import yaml from "yaml";
export function rulesForPhase(rulebookPath, phaseId) {
  const rb = yaml.parse(fs.readFileSync(rulebookPath, "utf8"));
  const seen = new Set(); const ordered = [];
  function addPhase(pid) {
    const p = rb.phases[pid]; if (!p) throw new Error(`unknown phase ${pid}`);
    for (const inh of (p.inherits||[])) addPhase(inh);
    if (Array.isArray(p.rules)) {
      for (const id of p.rules) {
        if (seen.has(id)) continue;
        const rule = rb.rules?.[id];
        if (!rule) throw new Error(`unknown rule ${id}`);
        seen.add(id);
        ordered.push({ id, ...rule });
      }
    } else if (p.rules && typeof p.rules === "object") {
      for (const [id, rule] of Object.entries(p.rules)) {
        if (seen.has(id)) continue;
        seen.add(id);
        ordered.push({ id, ...rule });
      }
    }
  }
  addPhase(phaseId); return ordered;
}
