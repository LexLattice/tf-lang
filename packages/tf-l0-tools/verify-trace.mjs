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

    for (const key of Object.keys(node)) {
      if (key === 'prim' || key === 'prim_id' || key === 'id') continue;
      stack.push(node[key]);
    }
  }

  return { names, fullIds };
}

function escapeRegexLiteral(text) {
  return text.replace(/[-/\^$*+?.()|[\]{}]/g, '\$&');
}

function compileManifestPattern(pattern) {
  if (typeof pattern !== 'string' || pattern.length === 0) return null;
  let regex = '^';
  for (let index = 0; index < pattern.length; ) {
    const char = pattern[index];
    if (char === ':' && pattern[index + 1] === '<') {
      const end = pattern.indexOf('>', index + 2);
      if (end === -1) {
        regex += escapeRegexLiteral(pattern.slice(index));
        break;
      }
      regex += '.*';
      index = end + 1;
      continue;
    }
    if (char === '<') {
      const end = pattern.indexOf('>', index + 1);
      if (end === -1) {
        regex += escapeRegexLiteral(pattern.slice(index));
        break;
      }
      regex += '[^/]+';
      index = end + 1;
      continue;
    }
    regex += escapeRegexLiteral(char);
    index += 1;
  }
  regex += '$';
  try {
    return new RegExp(regex);
  } catch (err) {
    return null;
  }
}

function compileManifestPatterns(manifest) {
  const writes = Array.isArray(manifest?.footprints_rw?.writes)
    ? manifest.footprints_rw.writes
    : [];
  const patterns = [];
  for (const entry of writes) {
    if (!entry || typeof entry.uri !== 'string') continue;
    const compiled = compileManifestPattern(entry.uri);
    if (compiled) {
      patterns.push(compiled);
    }
  }
  return patterns;
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

function normalizeHash(value) {
  return typeof value === 'string' && value ? value : null;
}

export async function verifyTrace({
  irPath,
  tracePath,
  manifestPath,
  catalogPath,
  statusPath,
  irHash,
  manifestHash,
  catalogHash,
}) {
  if (!irPath) {
    throw new Error('Missing --ir path');
  }
  if (!tracePath) {
    throw new Error('Missing --trace path');
  }

  const [irSource, traceSource, manifestSource, catalogSource, statusSource] = await Promise.all([
    readFile(irPath, 'utf8'),
    readFile(tracePath, 'utf8'),
    manifestPath ? readFile(manifestPath, 'utf8') : Promise.resolve(null),
    catalogPath ? readFile(catalogPath, 'utf8') : Promise.resolve(null),
    statusPath ? readFile(statusPath, 'utf8') : Promise.resolve(null),
  ]);

  const ir = JSON.parse(irSource);
  const manifest = manifestSource ? JSON.parse(manifestSource) : null;
  const catalog = catalogSource ? JSON.parse(catalogSource) : null;
  const status = statusSource ? JSON.parse(statusSource) : null;
  const catalogMaps = buildCatalogMaps(catalog);
  const allowed = collectAllowedPrims(ir, catalogMaps.byName);
  const allowedNames = Array.from(allowed.names);
  allowedNames.sort();
  const allowedFull = Array.from(allowed.fullIds);
  allowedFull.sort();

  const allowedNameSet = new Set(allowedNames);
  const allowedFullSet = new Set(allowedFull);

  const allowedWritePatterns = manifest ? compileManifestPatterns(manifest) : [];

  const issuesSet = new Set();
  let unknownCount = 0;
  let deniedCount = 0;
  let provenanceMismatchCount = 0;

  const statusProvenance =
    status && typeof status.provenance === 'object' && !Array.isArray(status.provenance)
      ? status.provenance
      : null;

  let expectedIrHash = normalizeHash(irHash);
  let expectedManifestHash = normalizeHash(manifestHash);
  let expectedCatalogHash = normalizeHash(catalogHash);

  if (statusPath && !statusProvenance) {
    issuesSet.add('status missing provenance');
  }

  if (statusProvenance) {
    const statusIr = normalizeHash(statusProvenance.ir_hash);
    const statusManifest = normalizeHash(statusProvenance.manifest_hash);
    const statusCatalog = normalizeHash(statusProvenance.catalog_hash);

    if (expectedIrHash) {
      if (!statusIr) {
        issuesSet.add('status missing provenance field: ir_hash');
        provenanceMismatchCount += 1;
      } else if (statusIr !== expectedIrHash) {
        issuesSet.add('status provenance mismatch: ir_hash');
        provenanceMismatchCount += 1;
      }
    } else if (statusIr) {
      expectedIrHash = statusIr;
    }

    if (expectedManifestHash) {
      if (!statusManifest) {
        issuesSet.add('status missing provenance field: manifest_hash');
        provenanceMismatchCount += 1;
      } else if (statusManifest !== expectedManifestHash) {
        issuesSet.add('status provenance mismatch: manifest_hash');
        provenanceMismatchCount += 1;
      }
    } else if (statusManifest) {
      expectedManifestHash = statusManifest;
    }

    if (expectedCatalogHash) {
      if (!statusCatalog) {
        issuesSet.add('status missing provenance field: catalog_hash');
        provenanceMismatchCount += 1;
      } else if (statusCatalog !== expectedCatalogHash) {
        issuesSet.add('status provenance mismatch: catalog_hash');
        provenanceMismatchCount += 1;
      }
    } else if (statusCatalog) {
      expectedCatalogHash = statusCatalog;
    }
  }

  const metaCheckEnabled = Boolean(expectedIrHash || expectedManifestHash || expectedCatalogHash);

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

    if (metaCheckEnabled) {
      const meta = parsed?.meta;
      const hasMeta = meta && typeof meta === 'object' && !Array.isArray(meta);
      if (!hasMeta) {
        issuesSet.add('trace missing provenance meta');
        provenanceMismatchCount += 1;
      } else {
        if (expectedIrHash) {
          const value = normalizeHash(meta.ir_hash);
          if (value !== expectedIrHash) {
            issuesSet.add('provenance mismatch: ir_hash');
            provenanceMismatchCount += 1;
          }
        }
        if (expectedManifestHash) {
          const value = normalizeHash(meta.manifest_hash);
          if (value !== expectedManifestHash) {
            issuesSet.add('provenance mismatch: manifest_hash');
            provenanceMismatchCount += 1;
          }
        }
        if (expectedCatalogHash) {
          const value = normalizeHash(meta.catalog_hash);
          if (value !== expectedCatalogHash) {
            issuesSet.add('provenance mismatch: catalog_hash');
            provenanceMismatchCount += 1;
          }
        }
      }
    }

    const primValue = parsed?.prim_id;
    const canonical = canonicalizePrimId(primValue);
    let known = false;
    if (canonical) {
      known = allowedFullSet.has(canonical);
    } else {
      const primName = typeof primValue === 'string' ? primValue : '';
      const normalizedName = normalizeName(primName);
      known = Boolean(normalizedName && allowedNameSet.has(normalizedName));
    }
    if (!known) {
      issuesSet.add(`unknown prim: ${primValue}`);
      unknownCount += 1;
      continue;
    }

    const primName = canonical
      ? extractNameFromCanonical(canonical)
      : typeof primValue === 'string'
        ? primValue
        : '';
    const isWrite = isStorageWrite(canonical, primName, catalogMaps);
    if (isWrite && manifest) {
      const uri = parsed?.args?.uri;
      const uriString = typeof uri === 'string' ? uri : '';
      if (!uriString) {
        issuesSet.add('write denied: (missing uri)');
        deniedCount += 1;
        continue;
      }
      let allowedUri = false;
      for (const pattern of allowedWritePatterns) {
        if (pattern.test(uriString)) {
          allowedUri = true;
          break;
        }
      }
      if (!allowedUri) {
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
      provenance_mismatches: provenanceMismatchCount,
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
