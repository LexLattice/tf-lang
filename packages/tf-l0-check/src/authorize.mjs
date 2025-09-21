const DEFAULT_OPTS = {
  warnUnused: false,
  strictWarnsFail: false
};

const PROTECTED_NAME_REGEX = /^(sign-data|encrypt|decrypt)$/i;

export function checkAuthorize(ir, catalog, rules, opts = {}) {
  const options = { ...DEFAULT_OPTS, ...(opts || {}) };
  const reasons = [];
  const warnings = [];
  const stack = [];

  function visit(node) {
    if (node == null) {
      return;
    }

    if (Array.isArray(node)) {
      for (const child of node) {
        visit(child);
      }
      return;
    }

    if (typeof node !== 'object') {
      return;
    }

    if (node.node === 'Prim') {
      handlePrim(node);
      return;
    }

    const isAuthorizeRegion = node.node === 'Region' && node.kind === 'Authorize';
    const children = Array.isArray(node.children) ? node.children : [];

    if (isAuthorizeRegion) {
      const scopes = extractScopes(node);
      const entry = { scopes, used: new Set() };
      stack.push(entry);
      for (const child of children) {
        visit(child);
      }
      stack.pop();

      if (options.warnUnused) {
        for (const scope of scopes) {
          if (!entry.used.has(scope)) {
            warnings.push(`auth: unused authorize scope "${scope}"`);
          }
        }
      }
      return;
    }

    for (const child of children) {
      visit(child);
    }
  }

  function handlePrim(node) {
    const analysis = classifyPrim(node, catalog, rules);
    if (!analysis) {
      return;
    }

    const { requiredScopes, display } = analysis;
    if (!Array.isArray(requiredScopes) || requiredScopes.length === 0) {
      return;
    }

    const availableScopes = collectAvailableScopes();
    if (availableScopes.length === 0) {
      reasons.push(`auth: ${display} requires Authorize{scope in [${formatScopes(requiredScopes)}]}`);
      return;
    }

    const matchedScope = findMatchingScope(requiredScopes);
    if (!matchedScope) {
      reasons.push(
        `auth: scope mismatch for ${display} (have [${formatScopes(availableScopes)}], need one of [${formatScopes(requiredScopes)}])`
      );
      return;
    }

    markScopeUsed(matchedScope);
  }

  function collectAvailableScopes() {
    const seen = [];
    for (const entry of stack) {
      for (const scope of entry.scopes) {
        if (!seen.includes(scope)) {
          seen.push(scope);
        }
      }
    }
    return seen;
  }

  function findMatchingScope(requiredScopes) {
    for (const entry of [...stack].reverse()) {
      for (const scope of entry.scopes) {
        if (requiredScopes.includes(scope)) {
          return scope;
        }
      }
    }
    return null;
  }

  function markScopeUsed(scope) {
    for (let i = stack.length - 1; i >= 0; i -= 1) {
      const entry = stack[i];
      if (entry.scopes.includes(scope)) {
        entry.used.add(scope);
        break;
      }
    }
  }

  visit(ir);

  const ok = reasons.length === 0 && (!options.strictWarnsFail || warnings.length === 0);
  return { ok, reasons, warnings };
}

function classifyPrim(node, catalog, rules) {
  const name = typeof node?.prim === 'string' ? node.prim : '';
  if (!name) {
    return null;
  }

  const lowerName = name.toLowerCase();
  const directId = extractCanonicalId(node);
  const catalogEntry = lookupCatalogPrimitive(lowerName, catalog);

  let canonicalId = directId || catalogEntry?.id || null;
  let requiredScopes = normalizeScopes(rules?.[canonicalId]);

  if (requiredScopes.length === 0 && catalogEntry && PROTECTED_NAME_REGEX.test(lowerName)) {
    const hasCryptoEffect = (catalogEntry.effects || []).some((effect) => typeof effect === 'string' && effect.toLowerCase() === 'crypto');
    if (hasCryptoEffect) {
      const fallback = findRuleForBaseName(lowerName, rules);
      if (fallback) {
        canonicalId = fallback.id;
        requiredScopes = fallback.scopes;
      }
    }
  }

  if (requiredScopes.length === 0) {
    return null;
  }

  const display = canonicalId || name;
  return { requiredScopes, display };
}

function extractCanonicalId(node) {
  const candidates = [
    node?.impl?.id,
    node?.impl?.canonical_id,
    node?.impl?.canonical?.id,
    node?.prim_id,
    node?.primId,
    node?.id
  ];

  for (const candidate of candidates) {
    if (typeof candidate === 'string' && candidate.length > 0) {
      return candidate;
    }
  }
  return null;
}

function lookupCatalogPrimitive(name, catalog) {
  const primitives = Array.isArray(catalog?.primitives) ? catalog.primitives : [];
  if (!name || primitives.length === 0) {
    return null;
  }

  const lowerName = name.toLowerCase();
  const direct = primitives.find((p) => typeof p?.name === 'string' && p.name.toLowerCase() === lowerName);
  if (direct) {
    return direct;
  }

  for (const prim of primitives) {
    const id = prim?.id;
    if (typeof id === 'string' && id.toLowerCase().endsWith(`/${lowerName}@1`)) {
      return prim;
    }
  }

  return null;
}

function findRuleForBaseName(baseName, rules) {
  if (!rules || typeof rules !== 'object') {
    return null;
  }

  const entries = Object.entries(rules);
  const regex = new RegExp(`/${baseName.replace(/[-/\\^$*+?.()|[\]{}]/g, '\\$&')}@\\d+$`, 'i');
  for (const [id, value] of entries) {
    if (typeof id === 'string' && regex.test(id)) {
      const scopes = normalizeScopes(value);
      if (scopes.length > 0) {
        return { id, scopes };
      }
    }
  }
  return null;
}

function normalizeScopes(value) {
  if (!Array.isArray(value)) {
    return [];
  }
  return value
    .map((scope) => (typeof scope === 'string' ? scope.trim() : ''))
    .filter((scope) => scope.length > 0);
}

function extractScopes(node) {
  const attrs = node?.attrs || {};
  const scopes = [];

  const addScope = (value) => {
    if (typeof value !== 'string' || value.length === 0) {
      return;
    }

    const segments = value.split(',');
    for (const raw of segments) {
      const scope = raw.trim();
      if (scope.length > 0) {
        scopes.push(scope);
      }
    }
  };

  if (Array.isArray(attrs.scope)) {
    for (const entry of attrs.scope) {
      addScope(entry);
    }
  } else if (attrs.scope !== undefined) {
    addScope(attrs.scope);
  }

  if (Array.isArray(attrs.scopes)) {
    for (const entry of attrs.scopes) {
      addScope(entry);
    }
  } else if (attrs.scopes !== undefined) {
    addScope(attrs.scopes);
  }

  return scopes;
}

function formatScopes(scopes) {
  return scopes.join(', ');
}
