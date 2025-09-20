export function validateCapabilities(manifest = {}, provided = {}) {
  const requiredEffects = Array.isArray(manifest?.required_effects)
    ? manifest.required_effects.slice()
    : [];
  const providedEffects = new Set(Array.isArray(provided?.effects) ? provided.effects : []);
  const missingEffects = requiredEffects
    .filter((effect) => !providedEffects.has(effect))
    .sort();

  const writes = Array.isArray(manifest?.footprints_rw?.writes)
    ? manifest.footprints_rw.writes
    : [];
  const prefixes = Array.isArray(provided?.allow_writes_prefixes) ? provided.allow_writes_prefixes : [];
  const denied = new Set();

  for (const entry of writes) {
    const uri = typeof entry?.uri === 'string' ? entry.uri : '';
    if (!uri) continue;
    if (prefixes.length === 0) {
      denied.add(uri);
      continue;
    }
    const allowed = prefixes.some((prefix) => typeof prefix === 'string' && uri.startsWith(prefix));
    if (!allowed) {
      denied.add(uri);
    }
  }

  const writeDenied = Array.from(denied).sort();
  const ok = missingEffects.length === 0 && writeDenied.length === 0;

  return {
    ok,
    missing_effects: missingEffects,
    write_denied: writeDenied,
  };
}

export default validateCapabilities;
