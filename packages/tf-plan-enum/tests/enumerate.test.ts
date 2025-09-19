import { readFile } from 'node:fs/promises';
import { fileURLToPath } from 'node:url';
import { resolve } from 'node:path';
import { describe, expect, it } from 'vitest';
import { enumeratePlanGraph } from '../src/index.js';

const specDir = resolve(fileURLToPath(new URL('.', import.meta.url)), '../../..', 'tests', 'specs');

async function loadSpec(name: string) {
  const file = resolve(specDir, name);
  const content = await readFile(file, 'utf-8');
  return JSON.parse(content);
}

describe('enumeratePlanGraph', () => {
  it('produces deterministic plan graphs', async () => {
    const spec = await loadSpec('demo.json');
    const first = enumeratePlanGraph(spec, { seed: 42 });
    const second = enumeratePlanGraph(spec, { seed: 42 });
    expect(first.nodes.length).toBeGreaterThanOrEqual(3);
    expect(first.nodes).toEqual(second.nodes);
  });

  it('supports beamWidth to limit results', async () => {
    const spec = await loadSpec('demo.json');
    const limited = enumeratePlanGraph(spec, { seed: 42, beamWidth: 2 });
    expect(limited.nodes.length).toBeLessThanOrEqual(2);
  });
});
