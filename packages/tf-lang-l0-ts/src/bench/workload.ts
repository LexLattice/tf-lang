import { DEV_PROOFS, emitTag, flush } from '../proof/index.js';
import type { ProofMeta } from '../proof/emit.js';

const TAG = { kind: 'Transport', op: 'LENS_PROJ', region: '/bench' } as const;

export function runWorkload(iterations: number): void {
  if (!DEV_PROOFS) {
    return;
  }
  for (let index = 0; index < iterations; index += 1) {
    const meta: ProofMeta = {
      runtime: 'ts',
      ts: Date.now(),
      region: TAG.region,
      gate: 'bench.workload',
      oracle: 'bench',
      seed: index,
    };
    emitTag(TAG, meta);
  }
  flush();
}
