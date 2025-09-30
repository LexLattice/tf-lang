import { proveStableCorrImpliesIdempotent } from '../packages/prover/z3.mjs';

export async function checkIdempotency({ publishNodes = [] } = {}) {
  const results = [];

  for (const meta of publishNodes) {
    const channel = typeof meta.node.channel === 'string' ? meta.node.channel : null;
    if (!channel || !channel.startsWith('rpc:req:')) {
      continue;
    }
    const hasCorr = Boolean(meta.hasCorr);
    const corrStable = Boolean(meta.corrStable);
    let proved = false;
    let reason = null;

    if (!hasCorr) {
      reason = 'missing-corr';
    } else if (!corrStable) {
      reason = 'unstable-corr';
    } else {
      try {
        proved = await proveStableCorrImpliesIdempotent({ hasCorr, corrStable });
        if (!proved) {
          reason = 'solver-failed';
        }
      } catch (error) {
        reason = 'solver-failed';
      }
    }

    const ok = hasCorr && corrStable && proved;
    results.push({
      id: meta.node.id,
      channel,
      hasCorr,
      corrStable,
      proved,
      ok,
      reason,
      corrRefs: meta.corrRefs ?? [],
      entropyRooted: Boolean(meta.entropyRooted),
    });
  }

  return {
    ok: results.every((entry) => entry.ok),
    results,
  };
}

export default checkIdempotency;
