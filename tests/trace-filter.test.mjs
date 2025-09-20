import { test } from 'node:test';
import assert from 'node:assert/strict';
import { spawn } from 'node:child_process';
import { readFile } from 'node:fs/promises';
import { fileURLToPath } from 'node:url';

const scriptPath = fileURLToPath(new URL('../packages/tf-l0-tools/trace-filter.mjs', import.meta.url));
const fixtureUrl = new URL('./fixtures/trace-sample.jsonl', import.meta.url);

async function runCli(args, input) {
  return await new Promise((resolve, reject) => {
    const child = spawn(process.execPath, [scriptPath, ...(args ?? [])], {
      stdio: ['pipe', 'pipe', 'pipe']
    });

    let stdout = '';
    let stderr = '';

    child.stdout.setEncoding('utf8');
    child.stdout.on('data', (chunk) => {
      stdout += chunk;
    });

    child.stderr.setEncoding('utf8');
    child.stderr.on('data', (chunk) => {
      stderr += chunk;
    });

    child.on('error', reject);
    child.on('close', (code) => {
      if (code !== 0) {
        reject(new Error(`trace-filter exited with code ${code}: ${stderr}`));
        return;
      }
      resolve({ stdout, stderr });
    });

    if (input) {
      child.stdin.write(input);
    }
    child.stdin.end();
  });
}

test('filters by prim id', async () => {
  const fixture = await readFile(fixtureUrl, 'utf8');
  const { stdout } = await runCli(['--prim=tf:resource/write-object@1'], fixture);
  const lines = stdout.trim().split('\n');
  assert.equal(lines.length, 2);
  const prims = lines.map((line) => JSON.parse(line).prim_id);
  assert.deepEqual(new Set(prims), new Set(['tf:resource/write-object@1']));
});

test('filters by effect and tag grep', async () => {
  const fixture = await readFile(fixtureUrl, 'utf8');
  const { stdout } = await runCli(['--effect=Network.Out', '--grep=orders'], fixture);
  const lines = stdout.trim().split('\n');
  assert.equal(lines.length, 2);
  for (const line of lines) {
    const record = JSON.parse(line);
    assert.equal(record.effect, 'Network.Out');
    const tagString = typeof record.tag === 'string' ? record.tag : JSON.stringify(record.tag);
    assert.ok(tagString.toLowerCase().includes('orders'));
  }
});

test('pretty output contains indentation', async () => {
  const fixture = await readFile(fixtureUrl, 'utf8');
  const { stdout } = await runCli(['--prim=tf:service/log@1', '--pretty'], fixture);
  assert.match(stdout, /\{\n\s+"prim_id"/);
  assert.match(stdout, /\n\s+"tag"/);
});

test('ignores invalid JSON lines without crashing', async () => {
  const input = '{"prim_id":"keep-me","effect":"Pure"}\nnot json at all\n{"prim_id":"discard-me","effect":"Pure"}\n';
  const { stdout } = await runCli(['--prim=keep-me'], input);
  const lines = stdout.trim().split('\n');
  assert.equal(lines.length, 1);
  const record = JSON.parse(lines[0]);
  assert.equal(record.prim_id, 'keep-me');
});
