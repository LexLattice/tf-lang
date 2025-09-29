#!/usr/bin/env node
import { promises as fs } from 'node:fs';
import path from 'node:path';

import { emitJson, logStep, parseArgs, UsageError } from './_shared.mjs';

const ROOT = process.cwd();
const PACK_MANIFEST = path.join(ROOT, 'out/0.5/release/pack.json');

async function readPackManifest({ dryRun }) {
  if (dryRun) {
    logStep('dry-run enabled: skipping pack manifest read');
    return null;
  }
  try {
    const raw = await fs.readFile(PACK_MANIFEST, 'utf8');
    return JSON.parse(raw);
  } catch (error) {
    if (error.code === 'ENOENT') {
      throw new Error(`pack manifest not found at ${path.relative(ROOT, PACK_MANIFEST)}`);
    }
    throw error;
  }
}

function summarizePackages(manifest) {
  if (!manifest?.packages) {
    return [];
  }
  return manifest.packages.map((pkg) => ({
    name: pkg.manifest?.name ?? null,
    version: pkg.manifest?.version ?? null,
    directory: pkg.directory ?? null,
    artifacts: (pkg.artifacts ?? []).map((artifact) => ({
      filename: artifact.filename ?? null,
      size: artifact.size ?? null,
      integrity: artifact.integrity ?? null,
      shasum: artifact.shasum ?? null,
    })),
  }));
}

async function main(argv) {
  const args = parseArgs(argv, {
    usage: 'node tools/release/snapshot-lanes.mjs [options]',
    description: 'Summarize release lanes using the generated pack manifest.',
    flags: {
      out: {
        description: 'Write the JSON summary to this path in addition to stdout.',
      },
      tag: {
        description: 'Tag identifier for the snapshot lane (e.g. nightly).',
      },
      dryRun: {
        description: 'Skip reading the pack manifest and emit an empty summary.',
      },
      range: false,
      verbose: {
        description: 'Emit progress information to stderr.',
      },
      quiet: {
        description: 'Suppress stdout emission of the JSON summary.',
      },
    },
  });

  if (args.help) {
    process.stdout.write(args.helpText);
    return args;
  }

  if (args.verbose) {
    process.env.RELEASE_VERBOSE = '1';
  }

  const manifest = await readPackManifest(args);
  const packages = summarizePackages(manifest);
  const lanes = [
    {
      id: args.tag ?? 'latest',
      packages,
    },
  ];

  const statusBody = await emitJson(
    {
      ok: true,
      tag: args.tag ?? null,
      lanes,
      source: manifest ? path.relative(ROOT, PACK_MANIFEST) : null,
    },
    args.out,
  );
  if (!args.quiet) {
    process.stdout.write(statusBody);
  }
  return args;
}

async function run() {
  let args;
  try {
    args = await main(process.argv.slice(2));
  } catch (error) {
    if (error instanceof UsageError) {
      if (error.message) {
        console.error(error.message);
      }
      if (error.helpText) {
        process.stderr.write(error.helpText);
      }
      process.exit(error.exitCode);
    }
    console.error(`snapshot-lanes failed: ${error.message}`);
    if (args) {
      const failureBody = await emitJson(
        { ok: false, error: error.message },
        args.out,
      );
      if (!args.quiet) {
        process.stdout.write(failureBody);
      }
    }
    process.exit(1);
  }
}

run();
