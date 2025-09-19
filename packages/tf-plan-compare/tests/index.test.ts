import { mkdtemp, writeFile, rm } from 'node:fs/promises';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { afterAll, describe, expect, it } from 'vitest';
import demoSpec from '../../../tests/specs/demo.json' with { type: 'json' };
import { enumeratePlan } from '@tf-lang/tf-plan-enum';
import { createScaffoldPlan } from '@tf-lang/tf-plan-scaffold-core';
import { generateComparison } from '../src/index.js';

const tempDirs: string[] = [];

async function createTempDir(): Promise<string> {
  const dir = await mkdtemp(join(tmpdir(), 'tf-compare-'));
  tempDirs.push(dir);
  return dir;
}

afterAll(async () => {
  await Promise.all(tempDirs.map((dir) => rm(dir, { recursive: true, force: true })));
});

describe('generateComparison', () => {
  it('produces report artifacts', async () => {
    const plan = enumeratePlan(demoSpec, { seed: 42, beamWidth: 2, maxBranches: 2 });
    const scaffold = createScaffoldPlan(plan.nodes, plan.meta, { template: 'dual-stack', top: 2 });
    const dir = await createTempDir();
    const planNdjsonPath = join(dir, 'plan.ndjson');
    const scaffoldPath = join(dir, 'index.json');
    const ndjson = plan.nodes.map((node) => JSON.stringify(node)).join('\n');
    await writeFile(planNdjsonPath, `${ndjson}\n`);
    await writeFile(scaffoldPath, `${JSON.stringify(scaffold, null, 2)}\n`);

    const outputs = await generateComparison({ planNdjsonPath, scaffoldPath, outDir: join(dir, 'out') });
    expect(outputs.report.branches.length).toBeGreaterThan(0);
  });
});
