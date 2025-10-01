import { proveStableCorrImpliesIdempotent } from '../packages/prover/z3.mjs';

const GOAL_ID = 'idempotency';

export async function checkIdempotency({ publishNodes = [], logEvidence } = {}) {
  const results = [];
  const scripts = [];

  for (const meta of publishNodes) {
    const channel = typeof meta.node.channel === 'string' ? meta.node.channel : null;
    if (!channel || !channel.startsWith('rpc:req:')) {
      continue;
    }
    const hasCorr = Boolean(meta.hasCorr);
    const corrStable = Boolean(meta.corrStable);
    let proved = false;
    let reason = null;

    const flags = { hasCorr, corrStable };
    let errorInfo = null;

    if (!hasCorr) {
      reason = 'missing-corr';
    } else if (!corrStable) {
      reason = 'unstable-corr';
    } else {
      try {
        const proof = await proveStableCorrImpliesIdempotent({ hasCorr, corrStable });
        proved = proof?.proved ?? false;
        if (proof?.script) {
          scripts.push({ id: meta.node.id, channel, script: proof.script });
        }
        if (!proved) {
          reason = 'solver-failed';
        }
      } catch (error) {
        reason = 'solver-failed';
        errorInfo = {
          message: error?.message ?? 'solver-failed',
          detail: error?.cause?.message ?? null,
          flags: error?.flags ?? flags,
        };
        if (error?.script) {
          scripts.push({ id: meta.node.id, channel, script: error.script });
        }
      }
    }

    const ok = hasCorr && corrStable && proved;
    results.push({
      goal: GOAL_ID,
      id: meta.node.id,
      channel,
      hasCorr,
      corrStable,
      proved,
      ok,
      reason,
      corrRefs: meta.corrRefs ?? [],
      entropyRooted: Boolean(meta.entropyRooted),
      flags,
      error: errorInfo,
    });
  }

  let evidence = null;
  if (typeof logEvidence === 'function' && scripts.length > 0) {
    const body = scripts
      .map((entry, index) => {
        const label = entry.id ? `${entry.id} ${entry.channel ?? ''}`.trim() : entry.channel ?? '(rpc)';
        return `; case ${index + 1}: ${label}\n${entry.script.trim()}`;
      })
      .join('\n\n');
    const path = await logEvidence(GOAL_ID, body);
    if (path) {
      evidence = { kind: 'smt2', path };
    }
  }

  return {
    goal: GOAL_ID,
    ok: results.every((entry) => entry.ok),
    results,
    evidence,
  };
}

export default checkIdempotency;
