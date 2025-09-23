import fs from "fs"; import yaml from "yaml";
export function rulesForPhase(rulebookPath, phaseId) {
  const rb = yaml.parse(fs.readFileSync(rulebookPath, "utf8"));
  const seen = new Set(); const ordered = [];
  function addPhase(pid) {
    const p = rb.phases[pid]; if (!p) throw new Error(`unknown phase ${pid}`);
    for (const inh of (p.inherits||[])) addPhase(inh);
    for (const id of (p.rules||[])) if (!seen.has(id)) { seen.add(id); ordered.push({ id, ...rb.rules[id] }); }
  }
  addPhase(phaseId); return ordered;
}
