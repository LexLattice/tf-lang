#!/usr/bin/env node
import { existsSync } from 'node:fs';
import { mkdir, readFile, rm, writeFile } from 'node:fs/promises';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';
import { spawnSync } from 'node:child_process';
import { generateRustCrate } from './generate-rs.mjs';

const HERE = dirname(fileURLToPath(import.meta.url));

function printUsage() {
  console.log('Usage: node scripts/generate-rs-run.mjs <ir.json> -o <output dir>');
}

async function main() {
  const args = process.argv.slice(2);
  if (args.length === 0 || args.includes('--help') || args.includes('-h')) {
    printUsage();
    return;
  }

  const irPath = resolve(args[0]);
  let outDir = null;
  for (let i = 1; i < args.length; i += 1) {
    const arg = args[i];
    if (arg === '-o' || arg === '--out' || arg === '--out-dir') {
      i += 1;
      outDir = args[i];
    } else {
      throw new Error(`Unknown argument: ${arg}`);
    }
  }

  if (!outDir) {
    throw new Error('Output directory required via -o or --out');
  }

  const resolvedOutDir = resolve(outDir);
  await mkdir(resolvedOutDir, { recursive: true });

  const { crateName } = await generateRustCrate(irPath, resolvedOutDir);
  console.log(`generated crate ${crateName} at ${resolvedOutDir}`);

  if (process.env.LOCAL_RUST) {
    const cargoResult = spawnSync('cargo', ['run', '--', '--ir', irPath], {
      cwd: resolvedOutDir,
      stdio: 'inherit',
      env: process.env,
    });
    if (cargoResult.status !== 0) {
      throw new Error('cargo run failed');
    }
    const traceSrc = join(resolvedOutDir, 'out', 'trace.jsonl');
    if (existsSync(traceSrc)) {
      const outTrace = join(resolvedOutDir, 'out', 'trace.jsonl');
      const data = await readFile(traceSrc, 'utf8');
      await writeFile(outTrace, data, 'utf8');
      console.log(`wrote trace ${outTrace}`);
    }
  } else {
    const tracePath = join(resolvedOutDir, 'out', 'trace.jsonl');
    await rm(tracePath, { force: true });
  }
}

main().catch((err) => {
  console.error(err && err.stack ? err.stack : err);
  process.exit(1);
});
