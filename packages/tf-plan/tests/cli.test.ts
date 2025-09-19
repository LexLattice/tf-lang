import { execFile } from 'node:child_process';
import { mkdtemp } from 'node:fs/promises';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { fileURLToPath } from 'node:url';
import { promisify } from 'node:util';
import { describe, expect, it } from 'vitest';

const run = promisify(execFile);
const cliPath = fileURLToPath(new URL('../dist/cli.js', import.meta.url));
const specPath = fileURLToPath(new URL('../../../tests/specs/demo.json', import.meta.url));

describe('tf-plan CLI', () => {
  it('enumerates plans into the target directory', async () => {
    const outDir = await mkdtemp(join(tmpdir(), 'tf-plan-'));
    const { stdout } = await run('node', [cliPath, 'enumerate', '--spec', specPath, '--seed', '42', '--beam', '3', '--out', outDir]);
    expect(stdout).toContain('Enumerated');
  });
});
