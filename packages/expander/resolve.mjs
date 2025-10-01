import { readFileSync } from 'node:fs';

let cachedRegistry;

function loadRegistry() {
  if (!cachedRegistry) {
    const baseUrl = new URL('../../instances/', import.meta.url);
    const urls = [
      new URL('registry.v2.json', baseUrl),
      new URL('registry.json', baseUrl)
    ];
    for (const url of urls) {
      try {
        const raw = readFileSync(url, 'utf-8');
        if (!raw) continue;
        cachedRegistry = JSON.parse(raw);
        break;
      } catch (err) {
        if (err?.code !== 'ENOENT' && typeof console !== 'undefined' && typeof console.warn === 'function') {
          console.warn(`instances: failed to load ${url.pathname}: ${err?.message ?? err}`);
        }
      }
    }
    if (!cachedRegistry) {
      cachedRegistry = { default: '@Memory', rules: [] };
    }
  }
  return cachedRegistry;
}

/** Normalize a channel value into a comparable string token. */
export function normalizeChannel(channel) {
  if (typeof channel === 'string') {
    return channel;
  }
  if (channel && typeof channel === 'object') {
    if (typeof channel.var === 'string') {
      return `@${channel.var}`;
    }
    if (channel.value != null) {
      return String(channel.value);
    }
  }
  return '';
}

/** Normalize QoS objects into a single comparable string. */
function normalizeQos(q) {
  if (!q) return '';
  if (typeof q === 'string') return q;
  if (typeof q === 'object') {
    return String(q.delivery ?? q.delivery_guarantee ?? q.mode ?? q.level ?? '');
  }
  return '';
}

function asArray(x) {
  return Array.isArray(x) ? x : x != null ? [x] : [];
}

function globMatch(pattern, value) {
  const text = String(value ?? '');
  const pat = String(pattern ?? '');
  if (!pat.includes('*')) return pat === text;
  const re = new RegExp(`^${pat.split('*').map((s) => s.replace(/[.*+?^${}()|[\]\\]/g, '\\$&')).join('.*')}$`, 'u');
  return re.test(text);
}

function matchRuleWhen(when = {}, ctx = {}) {
  const domains = asArray(when.domain);
  const qoses = asArray(when.qos).map(String);
  const channels = asArray(when.channel);

  if (domains.length && !domains.includes(ctx.domain)) return false;
  if (qoses.length && !qoses.includes(ctx.qos)) return false;
  if (channels.length && !channels.some((p) => globMatch(p, ctx.channel))) return false;
  return true;
}

/** Return the first matching rule's instance hint; rule order matters. */
export function selectInstance(node, override = {}) {
  const registry = override.registry ?? loadRegistry();
  const context = {
    domain: override.domain ?? node.runtime?.domain ?? inferDomainFromNode(node) ?? 'default',
    channel: normalizeChannel(override.channel ?? node.channel),
    qos: normalizeQos(override.qos ?? node.qos)
  };
  for (const rule of registry.rules || []) {
    if (matchRuleWhen(rule.when, context)) {
      return rule.use || (registry.default ?? '@Memory');
    }
  }
  if (registry.domains?.[context.domain]) {
    return registry.domains[context.domain];
  }
  return registry.default ?? '@Memory';
}

function inferDomainFromNode(node) {
  if (!node || typeof node !== 'object') {
    return undefined;
  }
  switch (node.kind) {
    case 'Publish':
    case 'Subscribe': {
      const channel = normalizeChannel(node.channel);
      if (channel.startsWith('rpc:')) return 'interaction';
      if (channel.startsWith('metric:')) return 'obs';
      if (channel.startsWith('policy:')) return 'policy';
      return undefined;
    }
    case 'Transform':
      return 'transform';
    case 'Keypair':
      return 'process';
    default:
      return undefined;
  }
}

export function annotateInstances({ nodes = [], domainOf, registry } = {}) {
  for (const node of nodes) {
    const runtime = { ...(node.runtime || {}) };
    let domain = runtime.domain;

    if (typeof domain !== 'string' || domain.length === 0) {
      const explicit = typeof domainOf === 'function' ? domainOf(node) : undefined;
      if (typeof explicit === 'string' && explicit.length > 0) {
        domain = explicit;
      } else {
        domain = inferDomainFromNode(node) ?? 'default';
      }
    }

    runtime.domain = domain ?? 'default';
    node.runtime = runtime;

    const instance = selectInstance(node, { domain: runtime.domain, registry });
    node.runtime = {
      ...runtime,
      instance,
    };
  }
  return nodes;
}

export default annotateInstances;
