import { test } from 'node:test';
import { strict as assert } from 'node:assert';
import { spawn } from 'node:child_process';
import { fileURLToPath } from 'node:url';
import { promises as fs } from 'node:fs';

const scriptPath = fileURLToPath(new URL('../packages/tf-l0-tools/trace-filter.mjs', import.meta.url));
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

test('filters by prim id', async () => {
  const fixture = await fs.readFile(fixturePath, 'utf8');
  const { code, stdout, stderr } = await runCli(['--prim=tf:resource/write-object@1'], { input: fixture });
  assert.equal(code, 0, stderr);
  const lines = stdout.trim().split('\n');
  assert.equal(lines.length, 2);
  for (const line of lines) {
    const parsed = JSON.parse(line);
    assert.equal(parsed.prim_id, 'tf:resource/write-object@1');
  }
});

test('filters by effect and tag substring', async () => {
  const fixture = await fs.readFile(fixturePath, 'utf8');
  const { code, stdout } = await runCli(['--effect=Network.Out', '--grep=orders'], { input: fixture });
  assert.equal(code, 0);
  const lines = stdout.trim().split('\n');
  assert.equal(lines.length, 1);
  const parsed = JSON.parse(lines[0]);
  assert.equal(parsed.prim_id, 'tf:integration/publish-topic@1');
  assert.equal(parsed.tag.topic, 'orders');
});

test('pretty printing emits multi-line JSON blocks', async () => {
  const fixture = await fs.readFile(fixturePath, 'utf8');
  const { code, stdout } = await runCli(['--effect=Pure', '--pretty'], { input: fixture });
  assert.equal(code, 0);
  assert.ok(/\n  "/.test(stdout), 'expected indented output');
  const matches = stdout.trim().match(/\{\n  /g) ?? [];
  assert.ok(matches.length >= 2, 'expected multiple pretty-printed records');
});

test('ignores invalid JSON lines without crashing', async () => {
  const lines = [
    '{"prim_id":"one","effect":"Pure","tag":"ok"}',
    'this is not json',
    '{"prim_id":"two","effect":"Pure","tag":"orders"}'
  ];
  const input = `${lines.join('\n')}\n`;
  const { code, stdout, stderr } = await runCli(['--effect=Pure', '--grep=orders'], { input });
  assert.equal(code, 0, stderr);
  const trimmed = stdout.trim();
  assert.ok(trimmed.length > 0);
  const parsed = JSON.parse(trimmed);
  assert.equal(parsed.prim_id, 'two');
});
