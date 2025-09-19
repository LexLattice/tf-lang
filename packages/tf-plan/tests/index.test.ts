import { createHash } from 'node:crypto';
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

    const hashFile = async (filePath: string): Promise<string> => {
      const data = await readFile(filePath);
      return createHash('sha256').update(data).digest('hex');
    };

    const initialPlanHash = await hashFile(planPath);
    const initialNdjsonHash = await hashFile(ndjsonPath);

    const rerun = await runEnumerateCommand({
      specPath,
      seed: 42,
      outDir: outputDir,
    });
    expect(rerun.meta.seed).toBe(42);
    const planHash = await hashFile(planPath);
    const ndjsonHash = await hashFile(ndjsonPath);
    expect(planHash).toBe(initialPlanHash);
    expect(ndjsonHash).toBe(initialNdjsonHash);

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
