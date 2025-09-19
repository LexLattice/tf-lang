import { it, expect, afterEach, beforeEach, vi } from 'vitest';
import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';

const __dirname = path.dirname(fileURLToPath(import.meta.url));
const vec = JSON.parse(fs.readFileSync(path.join(__dirname, '../../..', 'tests', 'proof_tags.json'), 'utf8'));

async function loadModules() {
  const [{ VM }, { DummyHost }, proof] = await Promise.all([
    import('../src/vm/index.js'),
    import('../src/host/memory.js'),
    import('../src/proof/index.js'),
  ]);
  return { VM, DummyHost, flush: proof.flush, reset: proof.resetDevProofsForTest };
}

beforeEach(() => {
  vi.resetModules();
});

afterEach(() => {
  delete process.env.DEV_PROOFS;
  vi.resetModules();
});

it('TS emits expected tags when enabled and none when disabled', async () => {
  process.env.DEV_PROOFS = '1';
  let modules = await loadModules();
  let vm = new modules.VM(modules.DummyHost);
  await vm.run(vec.bytecode);
  expect(modules.flush()).toEqual(vec.expected_tags);

  modules.reset();
  delete process.env.DEV_PROOFS;
  vi.resetModules();

  modules = await loadModules();
  vm = new modules.VM(modules.DummyHost);
  await vm.run(vec.bytecode);
  expect(modules.flush()).toEqual([]);
});
