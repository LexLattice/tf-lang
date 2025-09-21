function canonicalJson(value) {
  if (Array.isArray(value)) {
    return '[' + value.map(canonicalJson).join(',') + ']';
  }
  if (value && typeof value === 'object') {
    const keys = Object.keys(value).sort();
    return '{' + keys.map((key) => `${JSON.stringify(key)}:${canonicalJson(value[key])}`).join(',') + '}';
  }
  return JSON.stringify(value);
}

function normalizePrimId(value) {
  if (typeof value !== 'string') return null;
  const trimmed = value.trim();
  if (!trimmed) return null;
  const match = /^tf:([^/]+)\/([^@]+)@(\d+)$/i.exec(trimmed);
  if (!match) return null;
  const [, domain, name, major] = match;
  const lowerName = name.toLowerCase();
  return {
    normalized: `tf:${domain}/${lowerName}@${major}`,
    name: lowerName,
  };
}

function addPrimIdentifier(target, names, value) {
  if (typeof value !== 'string') return;
  const trimmed = value.trim();
  if (!trimmed) return;
  const normalized = normalizePrimId(trimmed);
  if (normalized) {
    target.add(normalized.normalized);
    names.add(normalized.name);
    return;
  }
  names.add(trimmed.toLowerCase());
}

function collectPrimIdentifiers(ir) {
  const full = new Set();
  const names = new Set();
  const stack = [ir];
  const seen = new WeakSet();
  while (stack.length) {
    const current = stack.pop();
    if (!current) continue;
    if (typeof current !== 'object') continue;
    if (seen.has(current)) continue;
    seen.add(current);
    if (Array.isArray(current)) {
      for (const entry of current) {
        stack.push(entry);
      }
      continue;
    }
    if (current.node === 'Prim') {
      if (typeof current.prim === 'string') {
        addPrimIdentifier(full, names, current.prim);
      }
      if (typeof current.prim_id === 'string') {
        addPrimIdentifier(full, names, current.prim_id);
      }
      if (typeof current.id === 'string') {
        addPrimIdentifier(full, names, current.id);
      }
    }
    for (const value of Object.values(current)) {
      if (value && typeof value === 'object') {
        stack.push(value);
      }
    }
  }
  return { full, names };
}

function buildWriteSets(catalog) {
  const full = new Set();
  const names = new Set();
  if (catalog && Array.isArray(catalog.primitives)) {
    for (const primitive of catalog.primitives) {
      if (!primitive) continue;
      const effects = Array.isArray(primitive.effects) ? primitive.effects : [];
      if (!effects.some((effect) => effect === 'Storage.Write')) {
        continue;
      }
      if (typeof primitive.id === 'string') {
        const normalized = normalizePrimId(primitive.id);
        if (normalized) {
          full.add(normalized.normalized);
          names.add(normalized.name);
        }
      }
      if (typeof primitive.name === 'string') {
        names.add(primitive.name.toLowerCase());
      }
    }
  }
  return { full, names, hasCatalog: Boolean(catalog) };
}

function isWritePrim(primId, writeSets) {
  if (!primId || typeof primId !== 'string') {
    return false;
  }
  const trimmed = primId.trim();
  if (!trimmed) return false;
  const normalized = normalizePrimId(trimmed);
  const name = normalized ? normalized.name : trimmed.toLowerCase();
  if (normalized && writeSets.full.has(normalized.normalized)) {
    return true;
  }
  if (writeSets.names.has(name)) {
    return true;
  }
  return /^(write-object|delete-object|compare-and-swap)$/.test(name);
}

function extractAllowedPrefixes(manifest) {
  const writes = manifest?.footprints_rw?.writes;
  if (!Array.isArray(writes)) {
    return [];
  }
  const prefixes = [];
  for (const entry of writes) {
    if (!entry) continue;
    let pattern = null;
    if (typeof entry === 'string') {
      pattern = entry;
    } else if (typeof entry.uri === 'string') {
      pattern = entry.uri;
    }
    if (!pattern) continue;
    const trimmed = pattern.trim();
    if (!trimmed) continue;
    const idxLt = trimmed.indexOf('<');
    const idxColonLt = trimmed.indexOf(':<');
    let cut = trimmed.length;
    if (idxLt >= 0) cut = Math.min(cut, idxLt);
    if (idxColonLt >= 0) cut = Math.min(cut, idxColonLt);
    const prefix = trimmed.slice(0, cut);
    if (prefix) {
      prefixes.push(prefix);
    }
  }
  prefixes.sort();
  return prefixes;
}

function isAllowedPrim(primId, primSets) {
  if (!primId || typeof primId !== 'string') {
    return false;
  }
  const trimmed = primId.trim();
  if (!trimmed) return false;
  const normalized = normalizePrimId(trimmed);
  if (normalized) {
    if (primSets.full.has(normalized.normalized)) {
      return true;
    }
    if (primSets.names.has(normalized.name)) {
      return true;
    }
    return false;
  }
  return primSets.names.has(trimmed.toLowerCase());
}

export function verifyTrace({ ir, trace, manifest = null, catalog = null }) {
  if (!ir || typeof ir !== 'object') {
    throw new Error('verify-trace: IR object required');
  }
  if (typeof trace !== 'string') {
    throw new Error('verify-trace: trace content required');
  }

  const primSets = collectPrimIdentifiers(ir);
  const writeSets = buildWriteSets(catalog);
  const prefixes = manifest ? extractAllowedPrefixes(manifest) : [];

  const issues = [];
  let unknownCount = 0;
  let deniedCount = 0;
  let records = 0;

  const lines = trace.split(/\r?\n/);
  for (let i = 0; i < lines.length; i++) {
    const raw = lines[i];
    if (!raw) continue;
    const trimmed = raw.trim();
    if (!trimmed) continue;
    let entry;
    try {
      entry = JSON.parse(trimmed);
    } catch {
      issues.push(`invalid json at line ${i + 1}`);
      continue;
    }
    records += 1;
    const primId = typeof entry?.prim_id === 'string' ? entry.prim_id : null;
    if (!primId || !isAllowedPrim(primId, primSets)) {
      unknownCount += 1;
      issues.push(`unknown prim: ${primId ?? '(missing)'}`);
    }
    if (manifest && primId && isWritePrim(primId, writeSets)) {
      const uri = entry?.args?.uri;
      if (typeof uri !== 'string' || uri.length === 0) {
        deniedCount += 1;
        issues.push('write denied: (missing uri)');
      } else if (prefixes.length === 0 || !prefixes.some((prefix) => uri.startsWith(prefix))) {
        deniedCount += 1;
        issues.push(`write denied: ${uri}`);
      }
    }
  }

  issues.sort((a, b) => a.localeCompare(b));

  const ok = issues.length === 0;
  return {
    ok,
    issues,
    counts: {
      records,
      unknown_prims: unknownCount,
      denied_writes: deniedCount,
    },
  };
}

export { canonicalJson };
