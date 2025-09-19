import { mkdtemp, readFile, rm } from 'node:fs/promises';
import { tmpdir } from 'node:os';
import { join, resolve } from 'node:path';
import { afterAll, describe, expect, it } from 'vitest';
import {
  runEnumerateCommand,
  runExportCommand,
  runScoreCommand,
} from '../src/index.js';

const tempDirs: string[] = [];

async function createTempDir(): Promise<string> {
  const dir = await mkdtemp(join(tmpdir(), 'tf-plan-'));
  tempDirs.push(dir);
  return dir;
}

afterAll(async () => {
  await Promise.all(tempDirs.map((dir) => rm(dir, { recursive: true, force: true })));
});

describe('tf-plan CLI helpers', () => {
  it('enumerates, scores, and exports deterministically', async () => {
    const outputDir = await createTempDir();
    const specPath = resolve(process.cwd(), '../../tests/specs/demo.json');
    const plan = await runEnumerateCommand({
      specPath,
      seed: 42,
      outDir: outputDir,
    });
    const planPath = join(outputDir, 'plan.json');
    const ndjsonPath = join(outputDir, 'plan.ndjson');
    const planFile = JSON.parse(await readFile(planPath, 'utf8'));
    expect(planFile.nodes.length).toEqual(plan.nodes.length);
    expect(planFile.meta.seed).toBe(42);

    const scoredPath = join(outputDir, 'plan.scored.json');
    await runScoreCommand({ planPath, outPath: scoredPath });
    const scoredFile = JSON.parse(await readFile(scoredPath, 'utf8'));
    expect(scoredFile.nodes[0].score.total).toBeGreaterThan(0);

    const exportPath = join(outputDir, 'export.ndjson');
    await runExportCommand({ planPath, ndjsonPath: exportPath });
    const ndjson = await readFile(exportPath, 'utf8');
    expect(ndjson.trim().split('\n').length).toBe(plan.nodes.length);
  });
});
