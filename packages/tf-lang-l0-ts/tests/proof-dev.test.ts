import { describe, it, expect, beforeEach } from 'vitest';
import { VM } from '../src/vm/index.js';
import type { Program } from '../src/model/bytecode.js';
import { DummyHost } from '../src/host/memory.js';
import { flush, reset, type ProofTag } from '../src/proof/index.js';
import fs from 'fs';
import path from 'path';
import { fileURLToPath } from 'url';

const __dirname = path.dirname(fileURLToPath(import.meta.url));
const vec = JSON.parse(
  fs.readFileSync(path.resolve(__dirname, '../../../tests/dev/proof_dev.json'), 'utf-8')
) as { bytecode: Program; tags: ProofTag[] };

const prog: Program = vec.bytecode;
const expectedTags: ProofTag[] = vec.tags;

describe('proof dev mode', () => {
  beforeEach(() => {
    delete process.env.DEV_PROOFS;
    reset();
  });

  it('emits expected tags when enabled', async () => {
    process.env.DEV_PROOFS = '1';
    const vm = new VM(DummyHost);
    await vm.run(prog);
    const tags = flush();
    expect(tags).toEqual(expectedTags);
  });

  it('no tags when disabled', async () => {
    const vm = new VM(DummyHost);
    await vm.run(prog);
    expect(flush()).toEqual([]);
  });

  it('caches env until reset', async () => {
    process.env.DEV_PROOFS = '1';
    const vm = new VM(DummyHost);
    await vm.run(prog);
    flush();
    delete process.env.DEV_PROOFS;
    await vm.run(prog);
    expect(flush().length).toBeGreaterThan(0);
    reset();
    await vm.run(prog);
    expect(flush()).toEqual([]);
  });
});
