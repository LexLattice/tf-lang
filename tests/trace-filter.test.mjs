import test from 'node:test';
import assert from 'node:assert/strict';
import { spawn } from 'node:child_process';
import { createReadStream } from 'node:fs';

const SCRIPT_PATH = 'packages/tf-l0-tools/trace-filter.mjs';
const FIXTURE_PATH = 'tests/fixtures/trace-sample.jsonl';

function runCli(args, { inputFile, input } = {}) {
  return new Promise((resolve, reject) => {
    const child = spawn('node', [SCRIPT_PATH, ...args], {
      stdio: ['pipe', 'pipe', 'inherit']
    });

    let stdout = '';
    child.stdout.setEncoding('utf8');
    child.stdout.on('data', chunk => {
      stdout += chunk;
    });

    child.on('error', reject);
    child.on('close', code => {
      if (code !== 0) {
        reject(new Error(`trace-filter exited with code ${code}`));
      } else {
        resolve(stdout);
      }
    });

    if (inputFile) {
      const stream = createReadStream(inputFile);
      stream.setEncoding('utf8');
      stream.on('error', reject);
      stream.pipe(child.stdin);
    } else if (typeof input === 'string') {
      child.stdin.end(input);
    } else {
      child.stdin.end();
    }
  });
}

test('filters by prim id', async () => {
  const output = await runCli(['--prim=tf:resource/write-object@1'], {
    inputFile: FIXTURE_PATH
  });

  const lines = output
    .split('\n')
    .map(line => line.trim())
    .filter(Boolean);

  assert.equal(lines.length, 2);
  for (const line of lines) {
    const entry = JSON.parse(line);
    assert.equal(entry.prim_id, 'tf:resource/write-object@1');
  }
});

test('filters by effect and tag substring (case-insensitive)', async () => {
  const output = await runCli(['--effect=Network.Out', '--grep=orders'], {
    inputFile: FIXTURE_PATH
  });

  const lines = output
    .split('\n')
    .map(line => line.trim())
    .filter(Boolean);

  assert.equal(lines.length, 1);
  const entry = JSON.parse(lines[0]);
  assert.equal(entry.effect.family, 'Network.Out');
  assert.ok(JSON.stringify(entry.tag).toLowerCase().includes('orders'));
});

test('pretty printing expands entries across multiple lines', async () => {
  const output = await runCli(
    ['--pretty', '--effect=Network.Out', '--grep=ORDERS'],
    { inputFile: FIXTURE_PATH }
  );

  assert.ok(output.includes('\n  "'));
  const compactOutput = output
    .split('\n')
    .map(line => line.trim())
    .filter(Boolean)
    .join('');
  const parsed = JSON.parse(compactOutput);
  assert.equal(parsed.effect.family, 'Network.Out');
});

test('ignores invalid json lines without crashing', async () => {
  const payload = [
    '{"prim_id":"tf:resource/write-object@1","effect":{"family":"Pure"}}',
    'this is not valid json',
    '{"prim_id":"tf:resource/write-object@1","effect":{"family":"Pure"}}'
  ].join('\n');

  const output = await runCli(['--prim=tf:resource/write-object@1'], {
    input: payload
  });

  const lines = output
    .split('\n')
    .map(line => line.trim())
    .filter(Boolean);

  assert.equal(lines.length, 2);
  for (const line of lines) {
    const entry = JSON.parse(line);
    assert.equal(entry.prim_id, 'tf:resource/write-object@1');
  }
});
