export function validateCapabilities(manifest = {}, provided = {}) {
  const requiredEffects = Array.isArray(manifest?.required_effects)
    ? manifest.required_effects.filter((value) => typeof value === 'string')
    : [];
  const availableEffects = new Set(
    Array.isArray(provided?.effects)
      ? provided.effects.filter((value) => typeof value === 'string')
      : []
  );

  const missingEffects = Array.from(new Set(requiredEffects.filter((effect) => !availableEffects.has(effect)))).sort();

  const prefixes = Array.isArray(provided?.allow_writes_prefixes)
    ? provided.allow_writes_prefixes.filter((value) => typeof value === 'string')
    : [];
  const writes = Array.isArray(manifest?.footprints_rw?.writes)
    ? manifest.footprints_rw.writes
    : [];

  const deniedWrites = new Set();
  for (const entry of writes) {
    const uri = entry && typeof entry.uri === 'string' ? entry.uri : null;
    if (!uri) continue;
    const allowed = prefixes.some((prefix) => uri.startsWith(prefix));
    if (!allowed) {
      deniedWrites.add(uri);
    }
  }

  const writeDenied = Array.from(deniedWrites).sort();
  const ok = missingEffects.length === 0 && writeDenied.length === 0;

  return {
    ok,
    missing_effects: missingEffects,
    write_denied: writeDenied,
  };
}

export default validateCapabilities;
