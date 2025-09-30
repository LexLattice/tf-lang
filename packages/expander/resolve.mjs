import { readFileSync } from 'node:fs';

let cachedRegistry;

function loadRegistry() {
  if (!cachedRegistry) {
    const url = new URL('../../instances/registry.json', import.meta.url);
    const raw = readFileSync(url, 'utf-8');
    cachedRegistry = JSON.parse(raw);
  }
  return cachedRegistry;
}

function normalizeChannel(channel) {
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

export function annotateInstances({ nodes = [], domainOf } = {}) {
  const registry = loadRegistry();
  const defaultInstance = registry.default || '@Memory';
  for (const node of nodes) {
    let domain = typeof domainOf === 'function' ? domainOf(node) : undefined;
    if (!domain) {
      domain = inferDomainFromNode(node);
    }
    if (!domain) {
      domain = 'default';
    }
    const instance = registry.domains?.[domain] || defaultInstance;
    node.runtime = {
      ...(node.runtime || {}),
      instance,
      domain,
    };
  }
  return nodes;
}

export default annotateInstances;
