let contextFactoryPromise = null;
let initFactory = null;

function boolLiteral(value) {
  return value ? 'true' : 'false';
}

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
  const script = buildIdempotencyScript(flags);
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

    return { proved: result === 'unsat', script };
  } catch (error) {
    const failure = new Error('solver-failed');
    failure.cause = error;
    failure.flags = { ...flags };
    failure.script = script;
    throw failure;
  }
}

function sanitizeSymbol(name) {
  if (!name) {
    return 'guard';
  }
  const cleaned = String(name)
    .trim()
    .replace(/[^A-Za-z0-9_]/g, '_')
    .replace(/_{2,}/g, '_');
  const symbol = cleaned.length > 0 ? cleaned : 'guard';
  return symbol.length > 64 ? symbol.slice(0, 64) : symbol;
}

function buildGuardExclusiveScript({ symbol, positiveNegated, negativeNegated }) {
  const guard = symbol || 'guard';
  const positive = positiveNegated ? `(not ${guard})` : guard;
  const negative = negativeNegated ? `(not ${guard})` : guard;
  return [
    '(set-logic QF_UF)',
    `(declare-const ${guard} Bool)`,
    `(assert ${positive})`,
    `(assert ${negative})`,
    '(check-sat)',
  ].join('\n');
}

function buildIdempotencyScript(flags) {
  return [
    '(set-logic QF_UF)',
    '(declare-const hasCorr Bool)',
    '(declare-const corrStable Bool)',
    '(declare-const idempotent Bool)',
    `(assert (= hasCorr ${boolLiteral(flags.hasCorr)}))`,
    `(assert (= corrStable ${boolLiteral(flags.corrStable)}))`,
    '(assert (= idempotent (and hasCorr corrStable)))',
    '(push)',
    '(assert hasCorr)',
    '(assert corrStable)',
    '(assert (not idempotent))',
    '(check-sat)',
    '(pop)',
  ].join('\n');
}

export async function proveGuardExclusive({ guardVar, positiveNegated = false, negativeNegated = true }) {
  if (!guardVar) {
    throw new Error('guardVar-required');
  }
  const symbol = sanitizeSymbol(guardVar);
  const script = buildGuardExclusiveScript({ symbol, positiveNegated, negativeNegated });
  try {
    const ctx = await getContext();
    const solver = new ctx.Solver();
    const guard = ctx.Bool.const(symbol);
    const positiveExpr = positiveNegated ? ctx.Not(guard) : guard;
    const negativeExpr = negativeNegated ? ctx.Not(guard) : guard;

    solver.push();
    solver.add(positiveExpr);
    solver.add(negativeExpr);
    const result = await solver.check();
    solver.pop();

    return { proved: result === 'unsat', script };
  } catch (error) {
    const failure = new Error('solver-failed');
    failure.cause = error;
    failure.flags = { guardVar, positiveNegated, negativeNegated };
    failure.script = script;
    throw failure;
  }
}

export default {
  proveStableCorrImpliesIdempotent,
  proveGuardExclusive,
};
