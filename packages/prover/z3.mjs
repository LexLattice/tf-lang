import { init } from 'z3-solver';

let contextFactoryPromise = null;

async function getContext() {
  if (!contextFactoryPromise) {
    contextFactoryPromise = init().then(({ Context }) => Context('tf:prover'));
  }
  try {
    return await contextFactoryPromise;
  } catch (error) {
    contextFactoryPromise = null;
    throw error;
  }
}

export async function proveStableCorrImpliesIdempotent(flags) {
  try {
    const ctx = await getContext();
    const solver = new ctx.Solver();
    const hasCorr = ctx.Bool.const('hasCorr');
    const corrStable = ctx.Bool.const('corrStable');
    const idempotent = ctx.Bool.const('idempotent');

    const asBool = (value) => ctx.Bool.val(Boolean(value));

    solver.add(hasCorr.eq(asBool(flags.hasCorr)));
    solver.add(corrStable.eq(asBool(flags.corrStable)));
    solver.add(idempotent.eq(ctx.And(hasCorr, corrStable)));

    solver.push();
    solver.add(ctx.And(hasCorr, corrStable, ctx.Not(idempotent)));
    const result = await solver.check();
    solver.pop();

    return result === 'unsat';
  } catch (error) {
    const failure = new Error('solver-failed');
    failure.cause = error;
    throw failure;
  }
}

export default {
  proveStableCorrImpliesIdempotent,
};
