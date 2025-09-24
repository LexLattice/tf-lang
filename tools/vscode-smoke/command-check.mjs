import assert from 'node:assert/strict';
import { existsSync } from 'node:fs';
import { spawnSync } from 'node:child_process';
import path from 'node:path';
import { pathToFileURL, fileURLToPath } from 'node:url';

const here = path.dirname(fileURLToPath(import.meta.url));
const repoRoot = path.resolve(here, '..', '..');
const distModule = path.resolve(repoRoot, 'clients/vscode-tf/dist/extension.js');

if (!existsSync(distModule)) {
  const build = spawnSync('pnpm', ['exec', 'tsc', '-p', 'clients/vscode-tf/tsconfig.json'], { cwd: repoRoot, stdio: 'inherit' });
  if ((build.status ?? 1) !== 0) {
    throw new Error('Failed to compile VS Code extension for smoke test');
  }
}

const { runSourceMapWorkflow } = await import(pathToFileURL(distModule).href);

async function main() {
  const calls = [];
  const fakeRange = {
    start: { line: 1, character: 2 },
    end: { line: 1, character: 10 }
  };
  const result = await runSourceMapWorkflow(
    { symbol: 'traceSymbol', file: '/tmp/example.tf' },
    async params => {
      calls.push({ kind: 'request', params });
      return fakeRange;
    },
    range => {
      calls.push({ kind: 'reveal', range });
    },
    message => {
      calls.push({ kind: 'notify', message });
    }
  );

  assert.deepEqual(result, fakeRange, 'Expected fake range to be returned');
  assert.equal(calls.length, 2, 'Expected request and reveal calls');
  assert.equal(calls[0].kind, 'request', 'First call should be request');
  assert.equal(calls[1].kind, 'reveal', 'Second call should be reveal');
  assert.deepEqual(calls[0].params, { symbol: 'traceSymbol', file: '/tmp/example.tf' });

  console.log(JSON.stringify({ ok: true, calls, range: result }));
}

main().catch(err => {
  console.error(err);
  process.exitCode = 1;
});
