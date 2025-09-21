#!/usr/bin/env node

import { readFile } from 'node:fs/promises';
import process from 'node:process';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { parseArgs } from 'node:util';
import { canonicalize } from '../../tf-l0-ir/src/hash.mjs';

const usage =
  'Usage: node packages/tf-compose/bin/tf-policy-auth.mjs check <flow.tf> [--catalog <path>] [--rules <path>] [--warn-unused] [--strict-warns]';

class CLIError extends Error {
  constructor(message, exitCode = 2) {
    super(message);
    this.exitCode = exitCode;
  }
}

async function main(argv) {
  const { values, positionals } = parseArgs({
    args: argv.slice(2),
    options: {
      catalog: { type: 'string' },
      rules: { type: 'string' },
      'warn-unused': { type: 'boolean' },
      'strict-warns': { type: 'boolean' }
    },
    allowPositionals: true
  });

  if (positionals.length === 0) {
    throw new CLIError('Missing command');
  }

  const command = positionals[0];
  if (command !== 'check') {
    throw new CLIError(`Unknown command: ${command}`);
  }

  if (positionals.length < 2) {
    throw new CLIError('Missing flow path');
  }
  if (positionals.length > 2) {
    throw new CLIError(`Unexpected argument: ${positionals[2]}`);
  }

  const flowPath = path.resolve(process.cwd(), positionals[1]);
  const warnUnused = Boolean(values['warn-unused']);
  const strictWarns = Boolean(values['strict-warns']);

  const [{ parseDSL }, { checkAuthorize }] = await Promise.all([
    import('../src/parser.mjs'),
    import('../../tf-l0-check/src/authorize.mjs')
  ]);

  let flowSource;
  try {
    flowSource = await readFile(flowPath, 'utf8');
  } catch (err) {
    const reason = err && typeof err.message === 'string' ? err.message : String(err);
    throw new CLIError(`Failed to read flow at ${flowPath}: ${reason}`, 1);
  }

  const ir = parseDSL(flowSource);

  const scriptDir = path.dirname(fileURLToPath(import.meta.url));
  const catalogPath = resolveCatalogPath(values.catalog, scriptDir);
  const rulesPath = resolveRulesPath(values.rules, scriptDir);

  const [catalog, rules] = await Promise.all([
    loadJson(catalogPath, 'catalog'),
    loadJson(rulesPath, 'rules')
  ]);

  const verdict = checkAuthorize(ir, catalog, rules, {
    warnUnused,
    strictWarnsFail: strictWarns
  });

  const payload = {
    ok: Boolean(verdict?.ok),
    reasons: [...(verdict?.reasons || [])],
    warnings: [...(verdict?.warnings || [])]
  };

  const output = `${canonicalize(payload)}\n`;
  process.stdout.write(output);

  if (!payload.ok) {
    process.exitCode = 1;
  }
}

function resolveCatalogPath(override, scriptDir) {
  if (typeof override === 'string' && override.length > 0) {
    return path.resolve(process.cwd(), override);
  }
  return path.resolve(scriptDir, '..', '..', 'tf-l0-spec', 'spec', 'catalog.json');
}

function resolveRulesPath(override, scriptDir) {
  if (typeof override === 'string' && override.length > 0) {
    return path.resolve(process.cwd(), override);
  }
  return path.resolve(scriptDir, '..', '..', 'tf-l0-check', 'rules', 'authorize-scopes.json');
}

async function loadJson(targetPath, label) {
  try {
    const contents = await readFile(targetPath, 'utf8');
    return JSON.parse(contents);
  } catch (err) {
    const reason = err && typeof err.message === 'string' ? err.message : String(err);
    throw new CLIError(`Failed to load ${label} JSON at ${targetPath}: ${reason}`, 1);
  }
}

main(process.argv).catch((err) => {
  const exitCode = err instanceof CLIError ? err.exitCode : 1;
  const message = err && typeof err.message === 'string' ? err.message : String(err);
  console.error(message);
  console.error(usage);
  process.exit(exitCode);
});
