import { test } from 'node:test';
import { strict as assert } from 'node:assert';
import { spawn } from 'node:child_process';
import { fileURLToPath } from 'node:url';
import { promises as fs } from 'node:fs';

const scriptPath = fileURLToPath(new URL('../packages/tf-l0-tools/trace-summary.mjs', import.meta.url));
const fixturePath = fileURLToPath(new URL('./fixtures/trace-sample.jsonl', import.meta.url));

async function runCli(args, { input } = {}) {
  return new Promise((resolve, reject) => {
    const child = spawn(process.execPath, [scriptPath, ...args], {
      stdio: ['pipe', 'pipe', 'pipe'],
    });

    let stdout = '';
    let stderr = '';

    child.stdout.setEncoding('utf8');
    child.stderr.setEncoding('utf8');

    child.stdout.on('data', (chunk) => {
      stdout += chunk;
    });

    child.stderr.on('data', (chunk) => {
      stderr += chunk;
    });

    child.on('error', reject);
    child.on('close', (code) => {
      resolve({ code, stdout, stderr });
    });

    if (input !== undefined) {
      child.stdin.end(input);
    } else {
      child.stdin.end();
    }
  });
}

test('summarizes traces into canonical JSON', async () => {
  const fixture = await fs.readFile(fixturePath, 'utf8');
  const { code, stdout, stderr } = await runCli([], { input: fixture });
  assert.equal(code, 0, stderr);
  const summary = JSON.parse(stdout.trim());
  assert.equal(summary.total, 7);
  assert.equal(summary.by_prim['tf:resource/write-object@1'], 2);
  assert.equal(summary.by_prim['tf:integration/publish-topic@1'], 2);
  assert.equal(summary.by_effect['Storage.Write'], 2);
  assert.equal(summary.by_effect['Network.Out'], 2);
});

test('top option limits output keys', async () => {
  const fixture = await fs.readFile(fixturePath, 'utf8');
  const { code, stdout } = await runCli(['--top=2'], { input: fixture });
  assert.equal(code, 0);
  const summary = JSON.parse(stdout.trim());
  assert.equal(Object.keys(summary.by_prim).length, 2);
  assert.equal(Object.keys(summary.by_effect).length, 2);
  assert(summary.by_effect['Network.Out'] >= 2);
});

test('pretty option produces indented output', async () => {
  const fixture = await fs.readFile(fixturePath, 'utf8');
  const { code, stdout } = await runCli(['--pretty'], { input: fixture });
  assert.equal(code, 0);
  assert.ok(/\n  "by_prim"/.test(stdout));
  const summary = JSON.parse(stdout);
  assert.equal(summary.total, 7);
});

test('malformed lines warn once unless quiet', async () => {
  const lines = [
    '{"prim_id":"one","effect":"Pure"}',
    'not-json',
    '{"prim_id":"two","effect":"Pure"}',
  ];
  const input = lines.join('\n') + '\n';

  const noisy = await runCli([], { input });
  assert.equal(noisy.code, 0, noisy.stderr);
  assert.equal(noisy.stderr, 'trace-summary: skipping malformed line\n');
  const noisySummary = JSON.parse(noisy.stdout.trim());
  assert.equal(noisySummary.total, 2);

  const quiet = await runCli(['--quiet'], { input });
  assert.equal(quiet.code, 0, quiet.stderr);
  assert.equal(quiet.stderr, '');
  const quietSummary = JSON.parse(quiet.stdout.trim());
  assert.deepEqual(quietSummary, noisySummary);
});
