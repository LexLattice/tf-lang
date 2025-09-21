import { readFile } from 'node:fs/promises';

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

function normalizeName(name) {
  return typeof name === 'string' ? name.toLowerCase() : '';
}

function canonicalizePrimId(id) {
  if (typeof id !== 'string') return null;
  const match = /^tf:([^/]+)\/([^@]+)@(\d+)$/i.exec(id.trim());
  if (!match) return null;
  const [, domain, name, major] = match;
  const canonicalDomain = domain.toLowerCase();
  const canonicalName = name.toLowerCase();
  return `tf:${canonicalDomain}/${canonicalName}@${major}`;
}

function extractNameFromCanonical(id) {
  const match = /^tf:[^/]+\/([^@]+)@\d+$/.exec(id);
  return match ? match[1] : '';
}

function collectAllowedPrims(ir, catalogNameMap) {
  const names = new Set();
  const fullIds = new Set();

  const stack = [ir];
  while (stack.length > 0) {
    const node = stack.pop();
    if (!node || typeof node !== 'object') continue;

    if (Array.isArray(node)) {
      for (const item of node) {
        stack.push(item);
      }
      continue;
    }

    if (node.node === 'Prim') {
      const value = node.prim ?? node.prim_id ?? node.id;
      if (typeof value === 'string') {
        const canonical = canonicalizePrimId(value);
        if (canonical) {
          fullIds.add(canonical);
          names.add(normalizeName(extractNameFromCanonical(canonical)));
        } else {
          const normalized = normalizeName(value);
          if (normalized) {
            names.add(normalized);
            const candidates = catalogNameMap?.get(normalized) || [];
            for (const candidate of candidates) {
              fullIds.add(candidate);
            }
          }
        }
      }
    }

    if (Array.isArray(node.children)) {
      for (const child of node.children) {
        stack.push(child);
      }
    }
  }

  return { names, fullIds };
}

function deriveAllowedWritePrefixes(manifest) {
  const writes = Array.isArray(manifest?.footprints_rw?.writes)
    ? manifest.footprints_rw.writes
    : [];
  const prefixes = [];
  for (const entry of writes) {
    if (!entry || typeof entry.uri !== 'string') continue;
    const uri = entry.uri;
    let cutoff = uri.length;
    const placeholderIndex = uri.indexOf('<');
    if (placeholderIndex !== -1 && placeholderIndex < cutoff) {
      cutoff = placeholderIndex;
    }
    let colonIndex = uri.indexOf(':');
    while (colonIndex !== -1) {
      const next = uri[colonIndex + 1];
      if (next === '<') {
        if (colonIndex < cutoff) {
          cutoff = colonIndex;
        }
        break;
      }
      colonIndex = uri.indexOf(':', colonIndex + 1);
    }
    prefixes.push(uri.slice(0, cutoff));
  }
  prefixes.sort();
  return prefixes;
}

function buildCatalogMaps(catalog) {
  const primitives = Array.isArray(catalog?.primitives) ? catalog.primitives : [];
  const byId = new Map();
  const byName = new Map();
  for (const prim of primitives) {
    if (!prim || typeof prim.id !== 'string') continue;
    const canonical = canonicalizePrimId(prim.id);
    if (!canonical) continue;
    byId.set(canonical, prim);
    const name = normalizeName(prim.name || extractNameFromCanonical(canonical));
    if (!name) continue;
    if (!byName.has(name)) {
      byName.set(name, []);
    }
    byName.get(name).push(canonical);
  }
  for (const list of byName.values()) {
    list.sort();
  }
  return { byId, byName };
}

function isStorageWrite(primCanonical, primName, catalogMaps) {
  if (catalogMaps?.byId && primCanonical && catalogMaps.byId.has(primCanonical)) {
    const entry = catalogMaps.byId.get(primCanonical);
    const effects = Array.isArray(entry.effects) ? entry.effects : [];
    if (effects.includes('Storage.Write')) {
      return true;
    }
  }
  const target = normalizeName(primName);
  if (!target) return false;
  return /^(write-object|delete-object|compare-and-swap)$/.test(target);
}

export async function verifyTrace({ irPath, tracePath, manifestPath, catalogPath }) {
  if (!irPath) {
    throw new Error('Missing --ir path');
  }
  if (!tracePath) {
    throw new Error('Missing --trace path');
  }

  const [irSource, traceSource, manifestSource, catalogSource] = await Promise.all([
    readFile(irPath, 'utf8'),
    readFile(tracePath, 'utf8'),
    manifestPath ? readFile(manifestPath, 'utf8') : Promise.resolve(null),
    catalogPath ? readFile(catalogPath, 'utf8') : Promise.resolve(null),
  ]);

  const ir = JSON.parse(irSource);
  const manifest = manifestSource ? JSON.parse(manifestSource) : null;
  const catalog = catalogSource ? JSON.parse(catalogSource) : null;
  const catalogMaps = buildCatalogMaps(catalog);
  const allowed = collectAllowedPrims(ir, catalogMaps.byName);
  const allowedNames = Array.from(allowed.names);
  allowedNames.sort();
  const allowedFull = Array.from(allowed.fullIds);
  allowedFull.sort();

  const allowedNameSet = new Set(allowedNames);
  const allowedFullSet = new Set(allowedFull);

  const allowedWritePrefixes = manifest ? deriveAllowedWritePrefixes(manifest) : [];

  const issuesSet = new Set();
  let unknownCount = 0;
  let deniedCount = 0;
  let records = 0;

  const lines = traceSource.split(/\r?\n/);
  for (const raw of lines) {
    const line = raw.trim();
    if (!line) continue;
    let parsed;
    try {
      parsed = JSON.parse(line);
    } catch (err) {
      issuesSet.add('malformed record');
      continue;
    }
    records += 1;
    const primValue = parsed?.prim_id;
    const canonical = canonicalizePrimId(primValue);
    const primName = canonical
      ? extractNameFromCanonical(canonical)
      : typeof primValue === 'string'
        ? primValue
        : '';
    const normalizedName = normalizeName(primName);
    const known = (canonical && allowedFullSet.has(canonical)) || (normalizedName && allowedNameSet.has(normalizedName));
    if (!known) {
      issuesSet.add(`unknown prim: ${primValue}`);
      unknownCount += 1;
      continue;
    }

    const isWrite = isStorageWrite(canonical, primName, catalogMaps);
    if (isWrite && manifest) {
      const uri = parsed?.args?.uri;
      const uriString = typeof uri === 'string' ? uri : '';
      if (!uriString) {
        issuesSet.add('write denied: (missing uri)');
        deniedCount += 1;
        continue;
      }
      let allowedPrefix = false;
      for (const prefix of allowedWritePrefixes) {
        if (uriString.startsWith(prefix)) {
          allowedPrefix = true;
          break;
        }
      }
      if (!allowedPrefix) {
        issuesSet.add(`write denied: ${uriString}`);
        deniedCount += 1;
      }
    }
  }

  const issues = Array.from(issuesSet);
  issues.sort();

  const result = {
    ok: issues.length === 0,
    issues,
    counts: {
      records,
      unknown_prims: unknownCount,
      denied_writes: deniedCount,
    },
  };

  return {
    result,
    canonical: canonicalJson(result),
    allowedPrims: {
      names: allowedNames,
      full: allowedFull,
    },
  };
}

export { canonicalJson };
