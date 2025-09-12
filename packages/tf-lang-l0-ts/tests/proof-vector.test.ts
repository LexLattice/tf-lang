import { it, expect, afterEach } from 'vitest';
import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { VM } from '../src/vm/index.js';
import { DummyHost } from '../src/host/memory.js';
import { flush, resetDevProofsForTest } from '../src/proof/index.js';

const __dirname = path.dirname(fileURLToPath(import.meta.url));
const vec = JSON.parse(fs.readFileSync(path.join(__dirname, '../../..', 'tests', 'proof_tags.json'), 'utf8'));

afterEach(() => {
  delete process.env.DEV_PROOFS;
  resetDevProofsForTest();
});

it('TS emits expected tags when enabled and none when disabled', async () => {
  process.env.DEV_PROOFS = '1';
  const vm = new VM(DummyHost);
  await vm.run(vec.bytecode);
  expect(flush()).toEqual(vec.expected_tags);

  resetDevProofsForTest();
  delete process.env.DEV_PROOFS;
  await vm.run(vec.bytecode);
  expect(flush()).toEqual([]);
});
