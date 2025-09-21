import { readFile } from 'node:fs/promises';
import { join, dirname } from 'node:path';
import { fileURLToPath } from 'node:url';
import { sha256OfCanonicalJson } from './lib/digest.mjs';

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

export async function verifyTrace({
  irPath,
  tracePath,
  manifestPath,
  catalogPath,
  statusPath,
  expectedIrHash,
  expectedManifestHash,
  expectedCatalogHash,
}) {
  if (!irPath) {
    throw new Error('Missing --ir path');
  }
  if (!tracePath) {
    throw new Error('Missing --trace path');
  }

  const issuesSet = new Set();

  const [irSource, traceSource, manifestSource, catalogSource, statusSource] = await Promise.all([
    readFile(irPath, 'utf8'),
    readFile(tracePath, 'utf8'),
    manifestPath ? readFile(manifestPath, 'utf8') : Promise.resolve(null),
    catalogPath ? readFile(catalogPath, 'utf8') : Promise.resolve(null),
    statusPath ? readFile(statusPath, 'utf8') : Promise.resolve(null),
  ]);

  const ir = JSON.parse(irSource);
  const manifest = manifestSource ? JSON.parse(manifestSource) : null;
  let catalog = catalogSource ? JSON.parse(catalogSource) : null;

  let status = null;
  if (statusSource) {
    try {
      status = JSON.parse(statusSource);
    } catch (err) {
      issuesSet.add('status parse error');
    }
  }

  const provenance = status && typeof status.provenance === 'object' && !Array.isArray(status.provenance)
    ? status.provenance
    : null;
  if (statusPath && !provenance) {
    issuesSet.add('status missing provenance');
  }

  let expectedIr = expectedIrHash || null;
  let expectedManifest = expectedManifestHash || null;
  let expectedCatalog = expectedCatalogHash || null;

  if (provenance) {
    if (!expectedIr && typeof provenance.ir_hash === 'string') {
      expectedIr = provenance.ir_hash;
    } else if (expectedIr && typeof provenance.ir_hash === 'string' && expectedIr !== provenance.ir_hash) {
      issuesSet.add(`status.ir_hash mismatch: ${provenance.ir_hash}`);
    }
    if (!expectedManifest && typeof provenance.manifest_hash === 'string') {
      expectedManifest = provenance.manifest_hash;
    } else if (expectedManifest && typeof provenance.manifest_hash === 'string' && expectedManifest !== provenance.manifest_hash) {
      issuesSet.add(`status.manifest_hash mismatch: ${provenance.manifest_hash}`);
    }
    if (!expectedCatalog && typeof provenance.catalog_hash === 'string') {
      expectedCatalog = provenance.catalog_hash;
    } else if (expectedCatalog && typeof provenance.catalog_hash === 'string' && expectedCatalog !== provenance.catalog_hash) {
      issuesSet.add(`status.catalog_hash mismatch: ${provenance.catalog_hash}`);
    }
  }

  if (!catalog && expectedCatalog) {
    const here = dirname(fileURLToPath(import.meta.url));
    const defaultPath = join(here, '..', 'tf-l0-spec', 'spec', 'catalog.json');
    try {
      const fallbackSource = await readFile(defaultPath, 'utf8');
      const fallback = JSON.parse(fallbackSource);
      const fallbackHash = sha256OfCanonicalJson(fallback);
      if (fallbackHash === expectedCatalog) {
        catalog = fallback;
        catalogPath = defaultPath;
      }
    } catch {}
  }

  const irHashActual = sha256OfCanonicalJson(ir);
  if (expectedIr && irHashActual !== expectedIr) {
    issuesSet.add(`ir_hash mismatch: expected ${expectedIr} actual ${irHashActual}`);
  }

  let manifestHashActual = null;
  if (manifest) {
      manifestHashActual = sha256OfCanonicalJson(manifest);
  }
  if (expectedManifest) {
    if (manifestHashActual) {
      if (manifestHashActual !== expectedManifest) {
        issuesSet.add(`manifest_hash mismatch: expected ${expectedManifest} actual ${manifestHashActual}`);
      }
    } else {
      issuesSet.add('manifest hash verification unavailable');
    }
  }

  let catalogHashActual = null;
  if (catalog) {
    catalogHashActual = sha256OfCanonicalJson(catalog);
  }
  if (expectedCatalog && catalogHashActual) {
    if (catalogHashActual !== expectedCatalog) {
      issuesSet.add(`catalog_hash mismatch: expected ${expectedCatalog} actual ${catalogHashActual}`);
    }
  }

  const catalogMaps = buildCatalogMaps(catalog);
  const allowed = collectAllowedPrims(ir, catalogMaps.byName);
  const allowedNames = Array.from(allowed.names);
  allowedNames.sort();
  const allowedFull = Array.from(allowed.fullIds);
  allowedFull.sort();

  const allowedNameSet = new Set(allowedNames);
  const allowedFullSet = new Set(allowedFull);

  const allowedWritePatterns = manifest ? compileManifestPatterns(manifest) : [];

  let unknownCount = 0;
  let deniedCount = 0;
  let metaMissingCount = 0;
  let metaMismatchCount = 0;
  let records = 0;

  const enforceMeta = Boolean(expectedIr || expectedManifest || expectedCatalog);

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
    let known = false;
    if (canonical) {
      known = allowedFullSet.has(canonical);
      if (!known) {
        const fallbackName = extractNameFromCanonical(canonical);
        const normalizedFallback = normalizeName(fallbackName);
        if (normalizedFallback && allowedNameSet.has(normalizedFallback)) {
          const candidates = catalogMaps.byName?.get(normalizedFallback);
          if (candidates && candidates.length > 0) {
            known = candidates.includes(canonical);
          }
        }
      }
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

    if (enforceMeta) {
      if (!parsed || typeof parsed.meta !== 'object' || Array.isArray(parsed.meta)) {
        issuesSet.add('missing_meta');
        metaMissingCount += 1;
      } else {
        const meta = parsed.meta;
        if (expectedIr && meta.ir_hash !== expectedIr) {
          issuesSet.add('hash_mismatch:ir_hash');
          metaMismatchCount += 1;
        }
        if (expectedManifest && meta.manifest_hash !== expectedManifest) {
          issuesSet.add('hash_mismatch:manifest_hash');
          metaMismatchCount += 1;
        }
        if (expectedCatalog && meta.catalog_hash !== expectedCatalog) {
          issuesSet.add('hash_mismatch:catalog_hash');
          metaMismatchCount += 1;
        }
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

  if (enforceMeta) {
    result.counts.meta_missing = metaMissingCount;
    result.counts.meta_mismatches = metaMismatchCount;
  }

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
