let contextFactoryPromise = null;
let initFactory = null;

async function loadInit() {
  if (initFactory) {
    return initFactory;
  }
  const module = await import('z3-solver');
  if (typeof module.init === 'function') {
    initFactory = module.init;
    return initFactory;
  }
  if (module.default && typeof module.default.init === 'function') {
    initFactory = module.default.init;
    return initFactory;
  }
  throw new Error('solver-init-missing');
}

async function getContext() {
  if (!contextFactoryPromise) {
    contextFactoryPromise = loadInit()
      .then((factory) => factory())
      .then(({ Context }) => Context('tf:prover'));
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
