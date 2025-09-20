#!/usr/bin/env node

import { access, mkdir, readFile, writeFile } from 'node:fs/promises';
import process from 'node:process';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { parseArgs } from 'node:util';
import { canonicalize } from '../../tf-l0-ir/src/hash.mjs';

const usage = 'Usage: node packages/tf-compose/bin/tf-policy.mjs check <flow.tf> [--forbid-outside] [--catalog path] [-o out.json]';

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
      'forbid-outside': { type: 'boolean' },
      catalog: { type: 'string' },
      out: { type: 'string', short: 'o' }
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

  const flowPath = positionals[1];
  const outPath = values.out ? path.resolve(process.cwd(), values.out) : null;
  const forbidOutside = Boolean(values['forbid-outside']);

  const [{ parseDSL }, { checkTransactions }] = await Promise.all([
    import('../src/parser.mjs'),
    import('../../tf-l0-check/src/txn.mjs')
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
  const catalogResolution = await resolveCatalogPath(values.catalog, scriptDir);

  let catalog;
  try {
    const contents = await readFile(catalogResolution, 'utf8');
    catalog = JSON.parse(contents);
  } catch (err) {
    console.error('warn: catalog not found or invalid; falling back to name-based detection');
    catalog = { primitives: [] };
  }

  let nameFallbackWarned = false;
  const verdict = checkTransactions(ir, catalog, {
    forbidWritesOutsideTxn: forbidOutside,
    onFallbackToNameDetection: () => {
      if (!nameFallbackWarned) {
        nameFallbackWarned = true;
        console.error('warn: using name-based detection; supply --catalog to avoid false negatives');
      }
    }
  });

  const payload = {
    ok: Boolean(verdict?.ok),
    reasons: [...(verdict?.reasons || [])]
  };

  const output = `${canonicalize(payload)}\n`;

  if (outPath) {
    await mkdir(path.dirname(outPath), { recursive: true });
    await writeFile(outPath, output, 'utf8');
  } else {
    process.stdout.write(output);
  }

  if (!payload.ok) {
    process.exitCode = 1;
  }
}

async function resolveCatalogPath(overridePath, scriptDir) {
  if (typeof overridePath === 'string' && overridePath.length > 0) {
    return path.resolve(process.cwd(), overridePath);
  }

  const repoRoot = await findRepoRoot(scriptDir);
  if (repoRoot) {
    return path.join(repoRoot, 'packages', 'tf-l0-spec', 'spec', 'catalog.json');
  }

  return path.resolve(scriptDir, '..', '..', 'tf-l0-spec', 'spec', 'catalog.json');
}

async function findRepoRoot(startDir) {
  let current = startDir;
  while (true) {
    const [hasWorkspace, hasGit] = await Promise.all([
      pathExists(path.join(current, 'pnpm-workspace.yaml')),
      pathExists(path.join(current, '.git'))
    ]);

    if (hasWorkspace || hasGit) {
      return current;
    }

    const parent = path.dirname(current);
    if (parent === current) {
      return null;
    }
    current = parent;
  }
}

async function pathExists(target) {
  try {
    await access(target);
    return true;
  } catch {
    return false;
  }
}

main(process.argv).catch((err) => {
  const exitCode = err instanceof CLIError ? err.exitCode : 1;
  const message = err && typeof err.message === 'string' ? err.message : String(err);
  console.error(message);
  console.error(usage);
  process.exit(exitCode);
});
