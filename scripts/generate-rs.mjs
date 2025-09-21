#!/usr/bin/env node
import { mkdir } from 'node:fs/promises';
import { dirname, basename, join, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';
import { spawn } from 'node:child_process';

const argv = process.argv.slice(2);
let irPath = null;
let outDir = null;
let name = null;

for (let i = 0; i < argv.length; i += 1) {
  const arg = argv[i];
  if (arg === '-o' || arg === '--out') {
    if (i + 1 >= argv.length) {
      throw new Error('generate-rs: expected path after -o/--out');
    }
    outDir = argv[i + 1];
    i += 1;
    continue;
  }
  if (arg === '--name') {
    if (i + 1 >= argv.length) {
      throw new Error('generate-rs: expected name after --name');
    }
    name = argv[i + 1];
    i += 1;
    continue;
  }
  if (!irPath && !arg.startsWith('-')) {
    irPath = arg;
    continue;
  }
  throw new Error(`generate-rs: unrecognized argument ${arg}`);
}

if (!irPath) {
  throw new Error('generate-rs: missing IR path argument');
}
if (!outDir) {
  throw new Error('generate-rs: missing output directory (use -o)');
}

const moduleDir = dirname(fileURLToPath(import.meta.url));
const repoRoot = resolve(moduleDir, '..');
const manifestPath = join(repoRoot, 'packages', 'tf-l0-codegen-rs', 'Cargo.toml');
const resolvedOut = resolve(outDir);
const resolvedIr = resolve(irPath);
const packageName = name ?? basename(resolvedOut);

await mkdir(resolvedOut, { recursive: true });

await runCargoGenerator(manifestPath, resolvedIr, resolvedOut, packageName);

async function runCargoGenerator(manifestPath, irFile, outDir, packageName) {
  const args = [
    'run',
    '--manifest-path',
    manifestPath,
    '--',
    '--ir',
    irFile,
    '--out',
    outDir,
    '--name',
    packageName,
  ];
  await new Promise((resolve, reject) => {
    const child = spawn('cargo', args, { stdio: 'inherit' });
    child.on('exit', (code) => {
      if (code === 0) {
        resolve();
      } else {
        reject(new Error(`cargo run exited with status ${code}`));
      }
    });
    child.on('error', (err) => reject(err));
  });
}
