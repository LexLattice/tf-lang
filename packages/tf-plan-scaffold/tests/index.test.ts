// @tf-test kind=product area=plan speed=fast deps=node

import { mkdtemp, writeFile, rm } from 'node:fs/promises';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { afterAll, describe, expect, it } from 'vitest';
import demoSpec from '../../../tests/specs/demo.json' with { type: 'json' };
import { enumeratePlan } from '@tf-lang/tf-plan-enum';
import { generateScaffold } from '../src/index.js';

const tempDirs: string[] = [];

async function createTempDir(): Promise<string> {
  const dir = await mkdtemp(join(tmpdir(), 'tf-scaffold-'));
  tempDirs.push(dir);
  return dir;
}

afterAll(async () => {
  await Promise.all(tempDirs.map((dir) => rm(dir, { recursive: true, force: true })));
});

describe('generateScaffold', () => {
  it('produces a scaffold plan from ndjson nodes', async () => {
    const plan = enumeratePlan(demoSpec, { seed: 42, beamWidth: 2, maxBranches: 3 });
    const dir = await createTempDir();
    const planJsonPath = join(dir, 'plan.json');
    const planNdjsonPath = join(dir, 'plan.ndjson');
    await writeFile(planJsonPath, `${JSON.stringify(plan, null, 2)}\n`);
    const ndjsonLines = plan.nodes.map((node) => JSON.stringify(node)).join('\n');
    await writeFile(planNdjsonPath, `${ndjsonLines}\n`);

    const outPath = join(dir, 'index.json');
    const scaffold = await generateScaffold({
      planNdjsonPath,
      planJsonPath,
      top: 2,
      template: 'dual-stack',
      outPath,
      seed: 42,
    });
    expect(scaffold.branches.length).toBeGreaterThan(0);
  });
});
