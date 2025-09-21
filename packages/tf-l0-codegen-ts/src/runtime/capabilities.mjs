function toStringArray(value) {
  if (!Array.isArray(value)) return [];
  return value.filter((entry) => typeof entry === 'string');
}

function uniqueSorted(values) {
  return Array.from(new Set(values)).sort();
}

function baseEffectName(effect) {
  if (typeof effect !== 'string') return '';
  const idx = effect.indexOf('.');
  return idx === -1 ? effect : effect.slice(0, idx);
}

function hasEffect(effects, effectFamily) {
  if (effects.size === 0) return true;
  if (effects.has(effectFamily)) return true;
  const base = baseEffectName(effectFamily);
  if (base && effects.has(base)) {
    return true;
  }
  return false;
}

export function assertAllowed(effectFamily, args = {}, provided = null) {
  if (!provided || typeof provided !== 'object') {
    return;
  }
  const allowedEffects = new Set(toStringArray(provided.effects));
  if (!hasEffect(allowedEffects, effectFamily)) {
    throw new Error(`capability denied: ${effectFamily}`);
  }
  if (effectFamily === 'Storage.Write') {
    const uri = typeof args?.uri === 'string' ? args.uri : '';
    if (uri.length === 0) {
      return;
    }
    const prefixes = toStringArray(provided.allow_writes_prefixes);
    if (prefixes.length === 0) {
      throw new Error(`capability denied: Storage.Write ${uri}`);
    }
    for (const prefix of prefixes) {
      if (uri.startsWith(prefix)) {
        return;
      }
    }
    throw new Error(`capability denied: Storage.Write ${uri}`);
  }
}

export function validateCapabilities(manifest = {}, provided = {}) {
  const requiredEffects = toStringArray(manifest?.required_effects);
  const providedEffects = new Set(toStringArray(provided?.effects));
  const missingEffects = requiredEffects.filter((effect) => !providedEffects.has(effect));

  const allowPrefixes = toStringArray(provided?.allow_writes_prefixes);
  const writes = Array.isArray(manifest?.footprints_rw?.writes) ? manifest.footprints_rw.writes : [];
  const denied = [];
  for (const entry of writes) {
    const uri = entry?.uri;
    if (typeof uri !== 'string' || uri.length === 0) {
      continue;
    }
    if (allowPrefixes.length === 0) {
      denied.push(uri);
      continue;
    }
    let allowed = false;
    for (const prefix of allowPrefixes) {
      if (uri.startsWith(prefix)) {
        allowed = true;
        break;
      }
    }
    if (!allowed) {
      denied.push(uri);
    }
  }

  const missing_effects = uniqueSorted(missingEffects);
  const write_denied = uniqueSorted(denied);

  return {
    ok: missing_effects.length === 0 && write_denied.length === 0,
    missing_effects,
    write_denied,
  };
}

export default validateCapabilities;
