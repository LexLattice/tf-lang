import { createReadStream } from 'node:fs';
import { readFile } from 'node:fs/promises';
import readline from 'node:readline';

const NAME_BASED_WRITE = /^(write-object|delete-object|compare-and-swap)$/i;

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

function normalizePrimKey(prim) {
  if (typeof prim !== 'string') return null;
  const match = /^tf:([^/]+)\/([^@]+)@(\d+)$/i.exec(prim);
  if (!match) return null;
  const domain = match[1].toLowerCase();
  const name = match[2].toLowerCase();
  const major = match[3];
  return `tf:${domain}/${name}@${major}`;
}

function barePrimName(prim) {
  if (typeof prim !== 'string') return null;
  const match = /^tf:[^/]+\/([^@]+)@(\d+)$/i.exec(prim);
  if (match) {
    return match[1].toLowerCase();
  }
  return prim.toLowerCase();
}

function collectPrimSet(ir) {
  const originals = new Set();
  const normalized = new Set();
  const bare = new Set();

  function record(value) {
    if (typeof value !== 'string') return;
    originals.add(value);
    const key = normalizePrimKey(value);
    if (key) {
      normalized.add(key);
      const name = barePrimName(value);
      if (name) {
        bare.add(name);
      }
    } else {
      bare.add(value.toLowerCase());
    }
  }

  function visit(node) {
    if (!node) return;
    if (Array.isArray(node)) {
      for (const item of node) {
        visit(item);
      }
      return;
    }
    if (typeof node === 'object') {
      if (typeof node.prim === 'string') {
        record(node.prim);
      }
      if (typeof node.prim_id === 'string') {
        record(node.prim_id);
      }
      for (const key of Object.keys(node)) {
        if (key === 'prim' || key === 'prim_id') continue;
        visit(node[key]);
      }
    }
  }

  visit(ir);
  const bareList = Array.from(bare).sort();
  return {
    originals,
    normalized,
    bare: new Set(bareList),
  };
}

function isPrimAllowed(primId, allowed) {
  if (typeof primId !== 'string') return false;
  if (allowed.originals.has(primId)) return true;
  const normalized = normalizePrimKey(primId);
  if (normalized && allowed.normalized.has(normalized)) return true;
  const bareName = barePrimName(primId);
  if (bareName && allowed.bare.has(bareName)) return true;
  return false;
}

function extractPrefix(pattern) {
  if (typeof pattern !== 'string') return '';
  const lt = pattern.indexOf('<');
  const colonBeforePlaceholder = pattern.indexOf(':<');
  let end = pattern.length;
  if (lt >= 0) {
    end = Math.min(end, lt);
  }
  if (colonBeforePlaceholder >= 0) {
    end = Math.min(end, colonBeforePlaceholder);
  }
  return pattern.slice(0, end);
}

function buildAllowedPrefixes(manifest) {
  const writes = manifest?.footprints_rw?.writes;
  if (!Array.isArray(writes) || writes.length === 0) {
    return [];
  }
  const set = new Set();
  for (const entry of writes) {
    if (entry && typeof entry.uri === 'string') {
      set.add(extractPrefix(entry.uri));
    }
  }
  return Array.from(set).sort();
}

function buildCatalogInfo(catalog) {
  if (!catalog || typeof catalog !== 'object') {
    return null;
  }
  const primitives = Array.isArray(catalog.primitives) ? catalog.primitives : [];
  const knownFull = new Set();
  const writeFull = new Set();
  const knownBare = new Set();
  const writeBare = new Set();

  for (const prim of primitives) {
    if (!prim || typeof prim !== 'object') continue;
    const id = typeof prim.id === 'string' ? prim.id : null;
    const name = typeof prim.name === 'string' ? prim.name : null;
    const effects = Array.isArray(prim.effects) ? prim.effects : [];
    const key = normalizePrimKey(id);
    const bareName = name ? name.toLowerCase() : barePrimName(id);
    const hasWrite = effects.some((effect) => effect === 'Storage.Write');

    if (key) {
      knownFull.add(key);
      if (hasWrite) {
        writeFull.add(key);
      }
    }
    if (bareName) {
      knownBare.add(bareName);
      if (hasWrite) {
        writeBare.add(bareName);
      }
    }
  }

  return { knownFull, writeFull, knownBare, writeBare };
}

function isWritePrim(primId, catalogInfo) {
  const name = barePrimName(primId);
  const normalized = normalizePrimKey(primId);

  if (catalogInfo) {
    if (normalized) {
      if (catalogInfo.writeFull.has(normalized)) {
        return true;
      }
      if (catalogInfo.knownFull.has(normalized)) {
        return false;
      }
    }
    if (name) {
      if (catalogInfo.writeBare.has(name)) {
        return true;
      }
      if (catalogInfo.knownBare.has(name)) {
        return false;
      }
    }
  }

  if (!name) return false;
  return NAME_BASED_WRITE.test(name);
}

export async function verifyTrace({
  irPath,
  tracePath,
  manifestPath,
  catalogPath,
}) {
  if (!irPath || !tracePath) {
    throw new Error('verifyTrace: irPath and tracePath are required');
  }

  const [irSource, manifestSource, catalogSource] = await Promise.all([
    readFile(irPath, 'utf8'),
    manifestPath ? readFile(manifestPath, 'utf8').catch((err) => { throw new Error(`failed to read manifest: ${err.message}`); }) : Promise.resolve(null),
    catalogPath ? readFile(catalogPath, 'utf8').catch((err) => { throw new Error(`failed to read catalog: ${err.message}`); }) : Promise.resolve(null),
  ]);

  let ir;
  try {
    ir = JSON.parse(irSource);
  } catch (err) {
    throw new Error(`failed to parse IR JSON: ${err.message}`);
  }

  let manifest;
  if (manifestSource !== null) {
    try {
      manifest = JSON.parse(manifestSource);
    } catch (err) {
      throw new Error(`failed to parse manifest JSON: ${err.message}`);
    }
  }

  let catalogInfo = null;
  if (catalogSource !== null) {
    let catalog;
    try {
      catalog = JSON.parse(catalogSource);
    } catch (err) {
      throw new Error(`failed to parse catalog JSON: ${err.message}`);
    }
    catalogInfo = buildCatalogInfo(catalog);
  }

  const allowed = collectPrimSet(ir);
  const prefixes = manifest ? buildAllowedPrefixes(manifest) : [];

  const rl = readline.createInterface({
    input: createReadStream(tracePath, { encoding: 'utf8' }),
    crlfDelay: Infinity,
  });

  const issues = [];
  let records = 0;
  let unknownPrims = 0;
  let deniedWrites = 0;
  let lineNumber = 0;

  try {
    for await (const rawLine of rl) {
      lineNumber += 1;
      const line = rawLine.trim();
      if (!line) continue;
      let record;
      try {
        record = JSON.parse(line);
      } catch (err) {
        issues.push(`invalid json at line ${lineNumber}`);
        continue;
      }
      records += 1;
      const primId = record?.prim_id;
      if (!isPrimAllowed(primId, allowed)) {
        const label = typeof primId === 'string' ? primId : '<missing>';
        issues.push(`unknown prim: ${label}`);
        unknownPrims += 1;
        continue;
      }

      if (!manifest) continue;
      if (!isWritePrim(primId, catalogInfo)) {
        continue;
      }

      const uri = record?.args?.uri;
      if (typeof uri !== 'string') {
        issues.push('write denied: <invalid uri>');
        deniedWrites += 1;
        continue;
      }
      if (prefixes.length === 0 || !prefixes.some((prefix) => uri.startsWith(prefix))) {
        issues.push(`write denied: ${uri}`);
        deniedWrites += 1;
      }
    }
  } catch (err) {
    throw new Error(`failed to read trace: ${err.message}`);
  }

  issues.sort();

  return {
    ok: issues.length === 0,
    issues,
    counts: {
      records,
      unknown_prims: unknownPrims,
      denied_writes: deniedWrites,
    },
  };
}

export function verifyTraceToJson(result) {
  return canonicalJson({
    ok: result.ok,
    issues: result.issues,
    counts: {
      records: result.counts.records,
      unknown_prims: result.counts.unknown_prims,
      denied_writes: result.counts.denied_writes,
    },
  });
}

export { canonicalJson };
