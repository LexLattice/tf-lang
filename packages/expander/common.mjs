import { parse as parseYaml } from 'yaml';

function parenBalance(str) {
  return (str.match(/\(/g) || []).length - (str.match(/\)/g) || []).length;
}

export function quoteCalls(src) {
  const lines = src.split(/\r?\n/);
  const out = [];
  for (let i = 0; i < lines.length; i += 1) {
    const line = lines[i];
    const match = line.match(/^(\s*(?:-\s+)?[A-Za-z0-9_]+:\s*)([A-Za-z0-9_.]+\()(.*)$/);
    if (match) {
      let call = match[2] + match[3];
      let depth = parenBalance(match[2]) + parenBalance(match[3]);
      while (depth > 0 && i + 1 < lines.length) {
        const next = lines[++i];
        call += `\n${next.trim()}`;
        depth += parenBalance(next);
      }
      call = call.replace(/\s*\n\s*/g, ' ');
      call = call.replace(/"/g, '\\"');
      out.push(`${match[1]}"${call}"`);
      continue;
    }
    out.push(line);
  }
  return out.join('\n');
}

export function parseCall(raw) {
  if (raw == null) throw new Error('missing macro invocation');
  if (typeof raw === 'object') {
    if (typeof raw.macro === 'string') {
      return { macro: raw.macro, args: raw.args ?? {} };
    }
    const entries = Object.entries(raw);
    if (entries.length !== 1) throw new Error(`invalid call object: ${JSON.stringify(raw)}`);
    const [macro, args] = entries[0];
    if (typeof args === 'string') return parseCall(args);
    if (Array.isArray(args)) return { macro, args: { __args: args } };
    return { macro, args: args ?? {} };
  }
  if (typeof raw !== 'string') throw new Error(`unsupported call type: ${typeof raw}`);
  const match = raw.match(/^([A-Za-z0-9_.]+)\((.*)\)$/);
  if (!match) throw new Error(`invalid call syntax: ${raw}`);
  const [, macro, argsRaw] = match;
  const trimmed = argsRaw.trim();
  if (!trimmed) return { macro, args: {} };
  if (trimmed.includes(':')) return { macro, args: parseYaml(`{ ${trimmed} }`) };
  const positional = parseYaml(`[${trimmed}]`);
  return { macro, args: { __args: positional } };
}

export function slug(value) {
  return String(value)
    .replace(/[^A-Za-z0-9_]+/g, '_')
    .replace(/_{2,}/g, '_')
    .replace(/^_+|_+$/g, '')
    .toLowerCase();
}

export function nodeId(prefix, index) {
  return `${prefix}_${index}`;
}

const EFFECT_MAP = {
  Publish: 'Outbound',
  Subscribe: 'Inbound',
  Keypair: 'Entropy',
  Transform: 'Pure',
};

export function computeEffects(nodes) {
  const seen = new Set();
  for (const node of nodes) {
    const effect = EFFECT_MAP[node.kind];
    if (!effect) throw new Error(`unsupported kernel kind: ${node.kind}`);
    seen.add(effect);
  }
  const order = ['Outbound', 'Inbound', 'Entropy', 'Pure'];
  const values = order.filter((effect) => seen.has(effect));
  if (values.length === 0) return 'Pure';
  return values.join('+');
}
