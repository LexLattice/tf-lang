#!/usr/bin/env node
import { spawn } from 'node:child_process';
import path from 'node:path';

const repoRoot = path.resolve('.');
const smokeScript = path.join(repoRoot, 'scripts', 'lsp-smoke', 'stdio.mjs');
const smokeCwd = path.join(repoRoot, 'out', '0.45', 'vscode');
const hoverFile = path.join(repoRoot, 'samples', 'a1', 'illegal_write.tf');

function runSmoke(args) {
  return new Promise((resolve, reject) => {
    const proc = spawn('node', [smokeScript, ...args], {
      cwd: smokeCwd,
      stdio: 'inherit'
    });
    proc.on('close', code => {
      if (code === 0) {
        resolve();
      } else {
        reject(new Error(`smoke failed: ${args.join(' ')}`));
      }
    });
  });
}

async function main() {
  await runSmoke(['--mode', 'init']);
  await runSmoke(['--mode', 'hover', '--file', hoverFile, '--symbol', 'tf:network/publish@1']);
}

main().catch(err => {
  console.error(err.stack || String(err));
  process.exit(1);
});
