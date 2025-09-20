import test from 'node:test';
import assert from 'node:assert/strict';
import { mkdtemp, writeFile } from 'node:fs/promises';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { fileURLToPath } from 'node:url';
import { promisify } from 'node:util';
import { execFile as execFileCallback } from 'node:child_process';

const execFile = promisify(execFileCallback);
const repoRoot = fileURLToPath(new URL('..', import.meta.url));
const tfCli = fileURLToPath(new URL('../packages/tf-compose/bin/tf.mjs', import.meta.url));

const flows = {
  storage: {
    file: fileURLToPath(new URL('../examples/flows/run_storage_ok.tf', import.meta.url)),
    expectEffect: 'Storage.Write',
    caps: {
      effects: ['Storage.Write', 'Pure', 'Observability'],
      allow_writes_prefixes: ['res://kv/'],
    },
  },
  publish: {
    file: fileURLToPath(new URL('../examples/flows/run_publish.tf', import.meta.url)),
    expectEffect: 'Network.Out',
    caps: {
      effects: ['Network.Out', 'Pure', 'Observability'],
      allow_writes_prefixes: [],
    },
  },
};

test('generated runner enforces capability manifests', async () => {
  const baseDir = await mkdtemp(join(tmpdir(), 'tf-runner-'));

  for (const [name, flow] of Object.entries(flows)) {
    const outDir = join(baseDir, name);
    await execFile('node', [tfCli, 'emit', flow.file, '--lang', 'ts', '--out', outDir], { cwd: repoRoot });

    const okCapsPath = join(baseDir, `${name}-caps.json`);
    await writeFile(okCapsPath, JSON.stringify(flow.caps), 'utf8');

    const { stdout: okStdout } = await execFile('node', [join(outDir, 'run.mjs'), '--caps', okCapsPath], { cwd: repoRoot });
    const okSummary = parseSummary(okStdout);
    assert.equal(okSummary.ok, true, `${name} flow should succeed with matching caps`);
    assert.ok(
      okSummary.effects.includes(flow.expectEffect),
      `${name} flow should record ${flow.expectEffect}`
    );

    const denyCapsPath = join(baseDir, `${name}-deny.json`);
    await writeFile(
      denyCapsPath,
      JSON.stringify({ effects: [], allow_writes_prefixes: [] }),
      'utf8'
    );

    const { stdout: denyStdout, stderr: denyStderr } = await execFile(
      'node',
      [join(outDir, 'run.mjs'), '--caps', denyCapsPath],
      { cwd: repoRoot }
    );
    const denySummary = parseSummary(denyStdout);
    assert.equal(denySummary.ok, false, `${name} flow should fail without caps`);
    assert.match(denyStderr, /(missing_effects|write_denied)/, `${name} flow should report missing caps`);
  }
});

function parseSummary(output) {
  const lines = output
    .split(/\r?\n/)
    .map((line) => line.trim())
    .filter(Boolean);
  if (lines.length === 0) {
    throw new Error('expected runner output');
  }
  const last = lines[lines.length - 1];
  return JSON.parse(last);
}
