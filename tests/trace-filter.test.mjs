import { strict as assert } from 'node:assert';
import { spawn } from 'node:child_process';
import { readFile, mkdtemp, writeFile } from 'node:fs/promises';
import { tmpdir } from 'node:os';
import { join, dirname } from 'node:path';
import test from 'node:test';
import { fileURLToPath } from 'node:url';

const __filename = fileURLToPath(import.meta.url);
const __dirname = dirname(__filename);
const repoRoot = dirname(__dirname);
const cliPath = join(repoRoot, 'packages', 'tf-l0-tools', 'trace-filter.mjs');
const fixturePath = join(repoRoot, 'tests', 'fixtures', 'trace-sample.jsonl');

async function runCli(input, args = [], options = {}) {
  return new Promise((resolve, reject) => {
    const proc = spawn(process.execPath, [cliPath, ...args], {
      cwd: options.cwd ?? repoRoot,
      stdio: ['pipe', 'pipe', 'pipe'],
    });

    let stdout = '';
    let stderr = '';
    proc.stdout.setEncoding('utf8');
    proc.stdout.on('data', (chunk) => {
      stdout += chunk;
    });
    proc.stderr.setEncoding('utf8');
    proc.stderr.on('data', (chunk) => {
      stderr += chunk;
    });

    proc.on('error', reject);
    proc.on('close', (code) => {
      if (code !== 0) {
        reject(new Error(`trace-filter exited with code ${code}: ${stderr}`));
        return;
      }
      resolve({ stdout, stderr });
    });

    proc.stdin.end(input);
  });
}

test('filters by prim id', async () => {
  const fixture = await readFile(fixturePath, 'utf8');
  const { stdout } = await runCli(fixture, ['--prim=tf:resource/write-object@1']);
  const lines = stdout.trim().split('\n').filter(Boolean);
  assert.equal(lines.length, 2, 'expected two write-object records');
  for (const line of lines) {
    const record = JSON.parse(line);
    assert.equal(record.prim_id, 'tf:resource/write-object@1');
  }
});

test('filters by effect and tag substring (case-insensitive)', async () => {
  const fixture = await readFile(fixturePath, 'utf8');
  const { stdout } = await runCli(fixture, ['--effect=Network.Out', '--grep=orders']);
  const lines = stdout.trim().split('\n').filter(Boolean);
  assert.equal(lines.length, 1, 'only the orders publish should match');
  const record = JSON.parse(lines[0]);
  assert.equal(record.effect, 'Network.Out');
  assert.match(JSON.stringify(record.tag).toLowerCase(), /orders/);
});

test('pretty printing expands JSON records', async () => {
  const fixture = await readFile(fixturePath, 'utf8');
  const { stdout } = await runCli(fixture, ['--prim=tf:resource/publish-event@1', '--pretty']);
  assert.match(stdout, /\{\n  "prim_id"/);
});

test('ignores invalid JSON lines without crashing', async () => {
  const tmpDir = await mkdtemp(join(tmpdir(), 'trace-filter-'));
  const malformedPath = join(tmpDir, 'input.jsonl');
  const payload = ['not json', '{"prim_id":"tf:resource/calc@1","effect":"Pure","tag":null}'];
  await writeFile(malformedPath, payload.join('\n'), 'utf8');
  const content = await readFile(malformedPath, 'utf8');
  const { stdout } = await runCli(content, ['--effect=Pure']);
  const lines = stdout.trim().split('\n').filter(Boolean);
  assert.equal(lines.length, 1);
  const record = JSON.parse(lines[0]);
  assert.equal(record.prim_id, 'tf:resource/calc@1');
});

test('CLI works when invoked from tool directory', async () => {
  const fixture = await readFile(fixturePath, 'utf8');
  const toolDir = join(repoRoot, 'packages', 'tf-l0-tools');
  const { stdout } = await runCli(fixture, ['--effect=Pure'], { cwd: toolDir });
  const lines = stdout.trim().split('\n').filter(Boolean);
  assert.equal(lines.length, 1);
  const record = JSON.parse(lines[0]);
  assert.equal(record.effect, 'Pure');
});
