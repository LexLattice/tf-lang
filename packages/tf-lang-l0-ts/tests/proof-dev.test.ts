import { describe, it, expect } from 'vitest';
import { VM } from '../src/vm/index.js';
import type { Program } from '../src/model/bytecode.js';
import { DummyHost } from '../src/host/memory.js';
import { withProofLog, resetDevProofsForTest } from '../src/proof/index.js';
import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';

const sample: Program = {
  version: '0.1',
  regs: 3,
  instrs: [
    { op: 'CONST', dst: 0, value: { x: 0 } },
    { op: 'LENS_PROJ', dst: 1, state: 0, region: '/x' },
    { op: 'CONST', dst: 2, value: 1 },
    { op: 'LENS_MERGE', dst: 0, state: 0, sub: 2, region: '/x' },
    { op: 'HALT' },
  ],
};

describe('proof dev mode', () => {
  it('emits tags when DEV_PROOFS=1', async () => {
    process.env.DEV_PROOFS = '1';
    resetDevProofsForTest();
    const vm = new VM(DummyHost);
    const { proofs } = await withProofLog(() => vm.run(sample));
    expect(proofs.some(t => t.kind === 'Transport')).toBe(true);
    expect(proofs.some(t => t.kind === 'Witness')).toBe(true);
    delete process.env.DEV_PROOFS;
  });

  it('no tags when DEV_PROOFS is unset', async () => {
    resetDevProofsForTest();
    const vm = new VM(DummyHost);
    const { proofs } = await withProofLog(() => vm.run(sample));
    expect(proofs.length).toBe(0);
  });

  it('caches env and supports reset', async () => {
    const vm = new VM(DummyHost);
    process.env.DEV_PROOFS = '1';
    resetDevProofsForTest();
    let res = await withProofLog(() => vm.run(sample));
    expect(res.proofs.length).toBeGreaterThan(0);
    process.env.DEV_PROOFS = '0';
    res = await withProofLog(() => vm.run(sample));
    expect(res.proofs.length).toBeGreaterThan(0); // still cached
    resetDevProofsForTest();
    res = await withProofLog(() => vm.run(sample));
    expect(res.proofs.length).toBe(0);
    delete process.env.DEV_PROOFS;
  });

  it('parallel logs are isolated', async () => {
    process.env.DEV_PROOFS = '1';
    resetDevProofsForTest();
    const vm = new VM(DummyHost);
    const run = () => withProofLog(() => vm.run(sample));
    const [a, b] = await Promise.all([run(), run()]);
    expect(a.proofs.length).toBeGreaterThan(0);
    expect(b.proofs.length).toBeGreaterThan(0);
    delete process.env.DEV_PROOFS;
  });

  it('matches shared vector tags', async () => {
    process.env.DEV_PROOFS = '1';
    resetDevProofsForTest();
    const __dirname = path.dirname(fileURLToPath(import.meta.url));
    const vec = JSON.parse(fs.readFileSync(path.join(__dirname, '../../../tests/proof-tags.json'), 'utf8'));
    const vm = new VM(DummyHost);
    const { proofs } = await withProofLog(() => vm.run(vec.program as Program));
    expect(proofs).toEqual(vec.expectedTags);
    delete process.env.DEV_PROOFS;
  });

  it('shared vector emits no tags when disabled', async () => {
    resetDevProofsForTest();
    const __dirname = path.dirname(fileURLToPath(import.meta.url));
    const vec = JSON.parse(fs.readFileSync(path.join(__dirname, '../../../tests/proof-tags.json'), 'utf8'));
    const vm = new VM(DummyHost);
    const { proofs } = await withProofLog(() => vm.run(vec.program as Program));
    expect(proofs.length).toBe(0);
  });
});
