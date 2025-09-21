import test from 'node:test';
import assert from 'node:assert/strict';
import { mkdtemp, readFile, readdir } from 'node:fs/promises';
import { tmpdir } from 'node:os';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { spawn } from 'node:child_process';

const __dirname = path.dirname(fileURLToPath(import.meta.url));
const repoRoot = path.resolve(__dirname, '..');

test('suite emits extended SMT laws deterministically', async () => {
  const baseDir = await mkdtemp(path.join(tmpdir(), 'smt-laws-'));
  const firstOut = path.join(baseDir, 'first');
  const secondOut = path.join(baseDir, 'second');

  await runSuite(firstOut);

  const writeLaw = await readFile(path.join(firstOut, 'write_idempotent_by_key.smt2'), 'utf8');
  assert.match(writeLaw, /\(assert \(not \(=/, 'write law should assert disequality');
  assert.ok(writeLaw.trim().endsWith('(check-sat)'), 'write law should end with check-sat');

  const inverseLaw = await readFile(path.join(firstOut, 'inverse_roundtrip.smt2'), 'utf8');
  assert.match(inverseLaw, /\(forall \(\(v Val\)\)/, 'inverse law should quantify over Val inputs');
  assert.match(inverseLaw, /\(forall \(\(b Bytes\)\)/, 'inverse law should quantify over Bytes inputs');
  assert.ok(inverseLaw.trim().endsWith('(check-sat)'), 'inverse law should end with check-sat');

  await runSuite(secondOut);

  const firstOutputs = await collectOutputs(firstOut);
  const secondOutputs = await collectOutputs(secondOut);
  assert.deepEqual(secondOutputs, firstOutputs, 'suite emission should be deterministic');
});

async function runSuite(outDir) {
  await new Promise((resolve, reject) => {
    const child = spawn(process.execPath, ['scripts/emit-smt-laws-suite.mjs', '-o', outDir], {
      cwd: repoRoot,
      stdio: ['ignore', 'pipe', 'pipe'],
    });
    const stderr = [];
    child.stderr.on('data', (chunk) => stderr.push(chunk));
    child.stdout.resume();
    child.on('error', reject);
    child.on('close', (code) => {
      if (code === 0) {
        resolve();
      } else {
        const message = Buffer.concat(stderr).toString('utf8');
        reject(new Error(`suite exited with ${code}: ${message}`));
      }
    });
  });
}

async function collectOutputs(dir) {
  const entries = await readdir(dir);
  entries.sort();
  const result = [];
  for (const name of entries) {
    const contents = await readFile(path.join(dir, name), 'utf8');
    result.push([name, contents]);
  }
  return result;
}

