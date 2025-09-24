#!/usr/bin/env node
import { spawn } from 'node:child_process';
import {
  cp,
  mkdir,
  rm,
  copyFile,
  mkdtemp,
  rename,
  readdir,
  utimes
} from 'node:fs/promises';
import { existsSync } from 'node:fs';
import path from 'node:path';
import os from 'node:os';
import { fileURLToPath } from 'node:url';

function run(command, args, options = {}) {
  return new Promise((resolve, reject) => {
    const proc = spawn(command, args, {
      stdio: 'inherit',
      ...options
    });
    proc.on('close', code => {
      if (code === 0) {
        resolve();
      } else {
        reject(new Error(`${command} ${args.join(' ')} exited with code ${code}`));
      }
    });
  });
}

async function ensureNodeModules(dir) {
  if (existsSync(path.join(dir, 'node_modules'))) {
    return;
  }
  await run('npm', ['install', '--no-package-lock'], { cwd: dir });
}

async function copyServerArtifacts(repoRoot, extensionRoot) {
  const source = path.join(repoRoot, 'packages', 'tf-lsp-server');
  const dest = path.join(extensionRoot, 'packages', 'tf-lsp-server');
  await run('pnpm', ['-C', source, 'run', 'build']);
  await rm(dest, { recursive: true, force: true });
  await mkdir(dest, { recursive: true });
  await cp(path.join(source, 'bin'), path.join(dest, 'bin'), { recursive: true });
  await cp(path.join(source, 'dist'), path.join(dest, 'dist'), { recursive: true });
  await cp(path.join(source, 'src'), path.join(dest, 'src'), { recursive: true });
  const deps = ['tf-compose', 'tf-l0-check', 'tf-l0-spec'];
  for (const name of deps) {
    const from = path.join(repoRoot, 'packages', name);
    const to = path.join(extensionRoot, 'packages', name);
    await rm(to, { recursive: true, force: true });
    await cp(from, to, { recursive: true });
  }
  return dest;
}

async function listEntries(dir, prefix = '') {
  const entries = await readdir(dir, { withFileTypes: true });
  entries.sort((a, b) => a.name.localeCompare(b.name));
  const results = [];
  for (const entry of entries) {
    const rel = prefix ? `${prefix}/${entry.name}` : entry.name;
    const full = path.join(dir, entry.name);
    if (entry.isDirectory()) {
      results.push(`${rel}/`);
      results.push(...(await listEntries(full, rel)));
    } else {
      results.push(rel);
    }
  }
  return results;
}

async function normalizeTimes(dir, mtime) {
  const entries = await readdir(dir, { withFileTypes: true });
  for (const entry of entries) {
    const full = path.join(dir, entry.name);
    if (entry.isDirectory()) {
      await normalizeTimes(full, mtime);
    }
    await utimes(full, mtime, mtime);
  }
  await utimes(dir, mtime, mtime);
}

async function zipFromList(cwd, target, entries) {
  await rm(target, { force: true });
  await new Promise((resolve, reject) => {
    const child = spawn('zip', ['-X', '-@', target], {
      cwd,
      stdio: ['pipe', 'inherit', 'inherit']
    });
    child.on('error', reject);
    child.on('close', code => {
      if (code === 0) {
        resolve();
      } else {
        reject(new Error(`zip exited with code ${code}`));
      }
    });
    for (const entry of entries) {
      child.stdin.write(`${entry}\n`);
    }
    child.stdin.end();
  });
}

async function makeDeterministicVSIX(vsixPath) {
  const tmpDir = await mkdtemp(path.join(os.tmpdir(), 'tf-vsix-'));
  const nondeterministic = `${vsixPath}.nondeterministic`;
  let restored = false;
  await rename(vsixPath, nondeterministic);
  try {
    await run('unzip', ['-q', nondeterministic, '-d', tmpDir]);
    const mtime = new Date('1980-01-01T00:00:00Z');
    await normalizeTimes(tmpDir, mtime);
    const entries = await listEntries(tmpDir);
    await zipFromList(tmpDir, vsixPath, entries);
    await rm(nondeterministic, { force: true });
    restored = true;
  } finally {
    if (!restored) {
      await rename(nondeterministic, vsixPath).catch(() => {});
    }
    await rm(tmpDir, { recursive: true, force: true });
  }
}

async function main() {
  const scriptDir = path.dirname(fileURLToPath(import.meta.url));
  const repoRoot = path.resolve(scriptDir, '..', '..');
  const extensionRoot = path.join(repoRoot, 'clients', 'vscode-tf');
  const outDir = path.join(repoRoot, 'out', '0.45', 'vscode');

  await ensureNodeModules(extensionRoot);
  await run('npm', ['run', 'build'], { cwd: extensionRoot });
  const bundledServerDir = await copyServerArtifacts(repoRoot, extensionRoot);

  await mkdir(outDir, { recursive: true });
  const vsixPath = path.join(outDir, 'clients-vscode-tf.vsix');
  await copyFile(path.join(repoRoot, 'LICENSE'), path.join(extensionRoot, 'LICENSE'));
  try {
    await run(
      'npx',
      [
        'vsce',
        'package',
        '--no-dependencies',
        '--allow-missing-repository',
        '--out',
        vsixPath
      ],
      { cwd: extensionRoot }
    );
  } finally {
    await rm(path.join(extensionRoot, 'LICENSE'), { force: true });
  }

  await makeDeterministicVSIX(vsixPath);

  const packageRoot = path.join(outDir, 'packages');
  await rm(packageRoot, { recursive: true, force: true });
  for (const name of ['tf-lsp-server', 'tf-compose', 'tf-l0-check', 'tf-l0-spec']) {
    const from = path.join(extensionRoot, 'packages', name);
    const to = path.join(packageRoot, name);
    await cp(from, to, { recursive: true });
  }
}

main().catch(err => {
  console.error(err.stack || String(err));
  process.exit(1);
});
