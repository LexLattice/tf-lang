#!/usr/bin/env node
import { promises as fs } from 'node:fs';
import path from 'node:path';

export class UsageError extends Error {
  constructor(message, { helpText } = {}) {
    super(message);
    this.name = 'UsageError';
    this.exitCode = 2;
    this.helpText = helpText ?? '';
  }
}

const DEFAULT_FLAGS = [
  { key: 'out', flag: '--out', type: 'value' },
  { key: 'dryRun', flag: '--dry-run', type: 'boolean' },
  { key: 'tag', flag: '--tag', type: 'value' },
  { key: 'range', flag: '--range', type: 'value' },
  { key: 'verbose', flag: '--verbose', type: 'boolean' },
  { key: 'json', flag: '--json', type: 'boolean', hidden: true },
  { key: 'quiet', flag: '--quiet', type: 'boolean' },
  { key: 'help', flag: '--help', type: 'boolean' },
];

function buildHelp(spec, flags) {
  const lines = [];
  if (spec?.usage) {
    lines.push(`Usage: ${spec.usage}`);
  }
  if (spec?.description) {
    lines.push('', spec.description);
  }
  const visible = flags.filter((entry) => !entry.hidden);
  if (visible.length) {
    lines.push('', 'Options:');
    for (const entry of visible) {
      const valueHint = entry.type === 'value' ? ' <value>' : '';
      const label = `${entry.flag}${valueHint}`;
      const padded = label.padEnd(24, ' ');
      const description = entry.description ?? '';
      lines.push(`  ${padded}${description}`);
    }
  }
  return `${lines.join('\n')}${lines.length ? '\n' : ''}`;
}

function resolveFlagSpec(spec = {}) {
  const overrides = spec.flags ?? {};
  const result = [];
  for (const base of DEFAULT_FLAGS) {
    const override = overrides[base.key] ?? overrides[base.flag];
    if (override === false) {
      continue;
    }
    const merged = {
      ...base,
      ...(typeof override === 'object' ? override : {}),
    };
    if (merged.type === 'boolean' && merged.default === undefined) {
      merged.default = false;
    }
    result.push(merged);
  }
  return result;
}

export function parseArgs(argv, spec = {}) {
  const flags = resolveFlagSpec(spec);
  const helpText = buildHelp(spec, flags);
  const options = {};
  const byFlag = new Map();

  for (const entry of flags) {
    if (entry.default !== undefined) {
      options[entry.key] = entry.default;
    } else if (entry.type === 'boolean') {
      options[entry.key] = false;
    } else {
      options[entry.key] = undefined;
    }
    byFlag.set(entry.flag, entry);
  }

  const positionals = [];

  for (let i = 0; i < argv.length; i += 1) {
    const token = argv[i];
    if (token === '--') {
      positionals.push(...argv.slice(i + 1));
      break;
    }
    const [flag, inlineValue] = token.split('=', 2);
    const entry = byFlag.get(flag);
    if (!entry) {
      throw new UsageError(`Unknown flag: ${flag}`, { helpText });
    }
    if (entry.type === 'boolean') {
      options[entry.key] = true;
      continue;
    }
    if (inlineValue !== undefined) {
      options[entry.key] = inlineValue;
      continue;
    }
    const next = argv[i + 1];
    if (next === undefined) {
      throw new UsageError(`Flag ${flag} requires a value`, { helpText });
    }
    options[entry.key] = next;
    i += 1;
  }

  for (const entry of flags) {
    if (entry.required && (options[entry.key] === undefined || options[entry.key] === null)) {
      throw new UsageError(`Flag ${entry.flag} is required`, { helpText });
    }
  }

  return { ...options, positionals, helpText };
}

export async function emitJson(payload, outPath) {
  const body = `${JSON.stringify(payload, null, 2)}\n`;
  if (outPath) {
    const target = path.isAbsolute(outPath) ? outPath : path.resolve(process.cwd(), outPath);
    await fs.mkdir(path.dirname(target), { recursive: true });
    await fs.writeFile(target, body, 'utf8');
  }
  return body;
}

export function logStep(message) {
  if (process.env.RELEASE_VERBOSE === '1') {
    process.stderr.write(`${message}\n`);
  }
}
