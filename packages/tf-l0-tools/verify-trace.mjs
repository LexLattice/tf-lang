#!/usr/bin/env node

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

function primVariants(prim) {
  if (typeof prim !== 'string') return [];
  const variants = new Set();
  const trimmed = prim.trim();
  if (!trimmed) return [];
  variants.add(trimmed);
  variants.add(trimmed.toLowerCase());

  const parts = trimmed.split('/');
  const last = parts[parts.length - 1] || '';
  const [namePart, versionPart] = last.split('@');
  const nameLower = (namePart || '').toLowerCase();
  const version = versionPart || '';
  if (nameLower) {
    variants.add(nameLower);
    if (version) {
      variants.add(`${nameLower}@${version}`);
    }
  }
  if (parts.length > 1) {
    const domain = parts.slice(0, -1).join('/').toLowerCase();
    if (nameLower) {
      const canonical = `${domain}/${nameLower}${version ? `@${version}` : ''}`;
      variants.add(canonical);
      if (canonical.startsWith('tf:')) {
        variants.add(canonical.slice(3));
      } else {
        variants.add(`tf:${canonical}`);
      }
    }
  }
  return Array.from(variants);
}

function collectPrimSet(ir, out = new Set()) {
  if (!ir || typeof ir !== 'object') {
    return out;
  }
  if (ir.node === 'Prim' && typeof ir.prim === 'string') {
    for (const variant of primVariants(ir.prim)) {
      out.add(variant);
    }
  }
  if (Array.isArray(ir.children)) {
    for (const child of ir.children) {
      collectPrimSet(child, out);
    }
  }
  for (const key of Object.keys(ir)) {
    if (key === 'children') continue;
    const value = ir[key];
    if (value && typeof value === 'object') {
      if (Array.isArray(value)) {
        for (const entry of value) {
          collectPrimSet(entry, out);
        }
      } else if (value.node) {
        collectPrimSet(value, out);
      }
    }
  }
  return out;
}

function toPrimKeySet(ir) {
  const variants = collectPrimSet(ir);
  const sorted = Array.from(variants).sort((a, b) => (a < b ? -1 : a > b ? 1 : 0));
  const result = new Set(sorted);
  return result;
}

function extractName(primId) {
  if (typeof primId !== 'string') return '';
  const parts = primId.split('/');
  const last = parts[parts.length - 1] || '';
  const [name] = last.split('@');
  return (name || '').toLowerCase();
}

function effectsForPrim(primId, catalog) {
  if (!catalog) return null;
  const primitives = Array.isArray(catalog.primitives) ? catalog.primitives : [];
  const lowerId = typeof primId === 'string' ? primId.toLowerCase() : '';
  const name = extractName(primId);
  for (const entry of primitives) {
    const entryId = typeof entry?.id === 'string' ? entry.id.toLowerCase() : '';
    const entryName = typeof entry?.name === 'string' ? entry.name.toLowerCase() : '';
    if (entryId && entryId === lowerId) {
      return Array.isArray(entry.effects) ? entry.effects : [];
    }
    if (name && entryName && entryName === name) {
      return Array.isArray(entry.effects) ? entry.effects : [];
    }
    if (name && entryId && entryId.endsWith(`/${name}${entryId.includes('@') ? entryId.slice(entryId.indexOf('@')) : ''}`)) {
      return Array.isArray(entry.effects) ? entry.effects : [];
    }
  }
  return null;
}

function isStorageWrite(primId, catalog) {
  const effects = effectsForPrim(primId, catalog);
  if (effects !== null) {
    return effects.some((effect) => effect === 'Storage.Write');
  }
  const name = extractName(primId);
  return /^(write-object|delete-object|compare-and-swap)$/.test(name);
}

function buildAllowedPrefixes(manifest) {
  const writes = manifest?.footprints_rw?.writes;
  if (!Array.isArray(writes)) return [];
  const prefixes = new Set();
  for (const entry of writes) {
    const uri = typeof entry?.uri === 'string' ? entry.uri : null;
    if (!uri) continue;
    const angle = uri.indexOf('<');
    if (angle !== -1) {
      prefixes.add(uri.slice(0, angle));
      continue;
    }
    const colon = uri.indexOf(':<');
    if (colon !== -1) {
      prefixes.add(uri.slice(0, colon));
      continue;
    }
    prefixes.add(uri);
  }
  return Array.from(prefixes).sort((a, b) => (a < b ? -1 : a > b ? 1 : 0));
}

export function verifyTrace(ir, traceRecords, options = {}) {
  const { manifest = null, catalog = null } = options;
  const primSet = toPrimKeySet(ir);
  const allowedPrefixes = manifest ? buildAllowedPrefixes(manifest) : [];

  let records = 0;
  let unknownPrims = 0;
  let deniedWrites = 0;
  const issues = [];

  for (const record of traceRecords) {
    if (!record || typeof record !== 'object') {
      continue;
    }
    records += 1;
    const primId = record.prim_id;
    const primIdStr = typeof primId === 'string' ? primId : '';

    let known = false;
    for (const variant of primVariants(primIdStr)) {
      if (primSet.has(variant)) {
        known = true;
        break;
      }
    }
    if (!known && primIdStr) {
      issues.push(`unknown prim: ${primIdStr}`);
      unknownPrims += 1;
    }

    if (manifest && isStorageWrite(primIdStr, catalog)) {
      const uriValue = record?.args?.uri;
      const uri = typeof uriValue === 'string' ? uriValue : '';
      let allowed = false;
      if (uri) {
        for (const prefix of allowedPrefixes) {
          if (uri.startsWith(prefix)) {
            allowed = true;
            break;
          }
        }
      }
      if (!allowed) {
        deniedWrites += 1;
        const display =
          typeof uriValue === 'string' && uriValue.length > 0 ? uriValue : '(missing uri)';
        issues.push(`write denied: ${display}`);
      }
    }
  }

  issues.sort((a, b) => (a < b ? -1 : a > b ? 1 : 0));

  const result = {
    ok: issues.length === 0,
    issues,
    counts: {
      records,
      unknown_prims: unknownPrims,
      denied_writes: deniedWrites,
    },
  };

  return result;
}

export { canonicalJson };

export default verifyTrace;
