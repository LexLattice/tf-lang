function toSortedArray(value) {
  if (!Array.isArray(value)) {
    return [];
  }
  return Array.from(new Set(value.filter((entry) => typeof entry === 'string'))).sort();
}

function extractWriteUris(manifest) {
  const writes = manifest?.footprints_rw?.writes;
  if (!Array.isArray(writes)) return [];
  const uris = [];
  for (const entry of writes) {
    if (entry && typeof entry === 'object' && typeof entry.uri === 'string') {
      uris.push(entry.uri);
    }
  }
  return uris.sort();
}

function normalizePrefixes(value) {
  if (!Array.isArray(value)) return [];
  return value.filter((entry) => typeof entry === 'string').sort();
}

export function validateCapabilities(manifest = {}, provided = {}) {
  const requiredEffects = toSortedArray(manifest?.required_effects || manifest?.effects);
  const providedEffects = new Set(toSortedArray(provided?.effects));
  const missingEffects = requiredEffects.filter((effect) => !providedEffects.has(effect));

  const writeUris = extractWriteUris(manifest);
  const prefixes = normalizePrefixes(provided?.allow_writes_prefixes);
  const deniedWrites = [];
  for (const uri of writeUris) {
    if (!prefixes.some((prefix) => uri.startsWith(prefix))) {
      deniedWrites.push(uri);
    }
  }

  deniedWrites.sort();

  return {
    ok: missingEffects.length === 0 && deniedWrites.length === 0,
    missing_effects: missingEffects,
    write_denied: deniedWrites
  };
}

export default validateCapabilities;
