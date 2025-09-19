import { emitTag } from './proof/emit.js';
import type { ProofMeta } from './proof/emit.js';
import { DEV_PROOFS } from './proof/flag.js';
import { pathToFileURL } from 'node:url';

export async function run(): Promise<void> {
  if (!DEV_PROOFS) {
    return;
  }
  for (let index = 0; index < 10; index += 1) {
    const meta: ProofMeta = {
      runtime: 'ts',
      ts: Date.now(),
      region: '/acct',
      oracle: 'Transport',
      seed: index,
    };
    emitTag({ kind: 'Transport', op: 'LENS_PROJ', region: `/acct/${index}` }, meta);
  }
  await new Promise((resolve) => setTimeout(resolve, 10));
}

const invokedDirectly = (() => {
  const entry = process.argv[1];
  if (!entry) return false;
  try {
    return import.meta.url === pathToFileURL(entry).href;
  } catch {
    return false;
  }
})();

if (invokedDirectly) {
  run().catch((error) => {
    process.stderr.write(`${error instanceof Error ? error.message : String(error)}\n`);
    process.exit(1);
  });
}
