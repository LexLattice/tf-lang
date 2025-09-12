import { describe, it, expect, beforeEach } from 'vitest';
import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { VM } from '../src/vm/index.js';
import { DummyHost } from '../src/host/memory.js';
import { flush, resetDevProofsForTest } from '../src/proof/index.js';
import type { Program } from '../src/model/bytecode.js';
import type { ProofTag } from '../src/proof/tags.js';

const __dirname = path.dirname(fileURLToPath(import.meta.url));
const vecPath = path.resolve(__dirname, '../../../tests/proof_tags.json');
const vec = JSON.parse(fs.readFileSync(vecPath, 'utf8')) as { bytecode: Program; expected_tags: ProofTag[] };

const prog = vec.bytecode;
const expected = vec.expected_tags;

describe('proof vector parity', () => {
  beforeEach(() => {
    resetDevProofsForTest();
    delete process.env.DEV_PROOFS;
  });

  it('matches expected tags when enabled', async () => {
    process.env.DEV_PROOFS = '1';
    const vm = new VM(DummyHost);
    await vm.run(prog);
    const tags = flush();
    expect(tags).toEqual(expected);
  });

  it('no tags when disabled', async () => {
    const vm = new VM(DummyHost);
    await vm.run(prog);
    const tags = flush();
    expect(tags).toEqual([]);
  });
});
