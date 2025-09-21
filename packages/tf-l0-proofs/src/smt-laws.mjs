const PRIMITIVES = {
  hash: {
    symbol: 'H',
    domain: 'Val',
    codomain: 'Val',
    pure: true
  },
  serialize: {
    symbol: 'S',
    domain: 'Val',
    codomain: 'Bytes',
    pure: true
  },
  deserialize: {
    symbol: 'D',
    domain: 'Bytes',
    codomain: 'Val',
    pure: true
  },
  'emit-metric': {
    symbol: 'E',
    domain: 'Val',
    codomain: 'Val',
    pure: false
  }
};

const FUNCTION_SIGNATURES = {
  H: { domain: ['Val'], codomain: 'Val' },
  S: { domain: ['Val'], codomain: 'Bytes' },
  D: { domain: ['Bytes'], codomain: 'Val' },
  E: { domain: ['Val'], codomain: 'Val' },
  P: { domain: ['Val'], codomain: 'Val' }
};

const LAW_BUILDERS = {
  'idempotent:hash'() {
    return {
      sorts: new Set(['Val']),
      functions: new Set(['H']),
      assertions: [
        '(assert (forall ((x Val)) (= (H (H x)) (H x))))'
      ]
    };
  },
  'inverse:serialize-deserialize'() {
    return {
      sorts: new Set(['Val', 'Bytes']),
      functions: new Set(['S', 'D']),
      assertions: [
        '(assert (forall ((v Val)) (= (D (S v)) v)))'
      ]
    };
  },
  'commute:emit-metric-with-pure'(context = {}) {
    const pureFns = Array.from(context.pureValFns || []);
    if (pureFns.length === 0) {
      return {
        sorts: new Set(['Val']),
        functions: new Set(['E', 'P']),
        assertions: [
          '(assert (forall ((x Val)) (= (E (P x)) (P (E x)))))'
        ]
      };
    }
    const assertions = pureFns
      .sort()
      .map(
        (fn) =>
          `(assert (forall ((x Val)) (= (E (${fn} x)) (${fn} (E x)))))`
      );
    return {
      sorts: new Set(['Val']),
      functions: new Set(['E', ...pureFns]),
      assertions
    };
  }
};

export function emitLaw(law, opts = {}) {
  const builder = LAW_BUILDERS[law];
  if (!builder) {
    throw new Error(`Unknown law: ${law}`);
  }
  const { sorts, functions, assertions } = builder(opts.context);
  const body = [];
  body.push(...declareSorts(sorts));
  body.push(...declareFunctions(functions));
  body.push(...assertions);
  body.push('(check-sat)');
  return body.join('\n') + '\n';
}

export function emitFlowEquivalence(irA, irB, lawSet = []) {
  const flowA = analyzeFlow(irA);
  const flowB = analyzeFlow(irB);

  if (flowA.sort !== flowB.sort) {
    throw new Error(
      `Flow sort mismatch: ${flowA.sort ?? 'unknown'} vs ${flowB.sort ?? 'unknown'}`
    );
  }

  const sorts = new Set(['Val']);
  const functions = new Set();
  const assertions = [];

  addAll(sorts, flowA.sorts);
  addAll(sorts, flowB.sorts);
  addAll(functions, flowA.functions);
  addAll(functions, flowB.functions);

  const pureValFns = new Set([...flowA.pureValFns, ...flowB.pureValFns]);

  for (const law of lawSet) {
    const builder = LAW_BUILDERS[law];
    if (!builder) {
      throw new Error(`Unknown law: ${law}`);
    }
    const { sorts: lawSorts, functions: lawFns, assertions: lawAssertions } =
      builder({ pureValFns });
    addAll(sorts, lawSorts);
    addAll(functions, lawFns);
    assertions.push(...lawAssertions);
  }

  const body = [];
  body.push(...declareSorts(sorts));
  body.push(...declareFunctions(functions));
  body.push('(declare-const x Val)');
  body.push(`(define-fun outA () ${flowA.sort} ${flowA.term})`);
  body.push(`(define-fun outB () ${flowB.sort} ${flowB.term})`);
  body.push(...assertions);
  body.push('(assert (not (= outA outB)))');
  body.push('(check-sat)');
  return body.join('\n') + '\n';
}

function analyzeFlow(ir) {
  const stages = Array.isArray(ir) ? ir : parseFlow(ir);
  const functions = new Set();
  const sorts = new Set();
  const pureValFns = new Set();

  let term = 'x';
  let sort = 'Val';

  for (const stage of stages) {
    const prim = PRIMITIVES[stage];
    if (!prim) {
      throw new Error(`Unsupported primitive in flow: ${stage}`);
    }
    if (prim.domain !== sort) {
      throw new Error(`Sort mismatch for ${stage}: expected ${prim.domain}, saw ${sort}`);
    }
    functions.add(prim.symbol);
    sorts.add(prim.domain);
    sorts.add(prim.codomain);
    if (prim.pure && prim.domain === 'Val' && prim.codomain === 'Val') {
      pureValFns.add(prim.symbol);
    }
    term = `(${prim.symbol} ${term})`;
    sort = prim.codomain;
  }

  return { term, sort, functions, sorts, pureValFns };
}

function parseFlow(value) {
  if (typeof value === 'string') {
    return value
      .split('|>')
      .map((part) => part.trim())
      .filter((part) => part.length > 0)
      .map((part) => {
        const match = part.match(/^([a-zA-Z0-9_-]+)/);
        if (!match) {
          throw new Error(`Unable to parse flow segment: ${part}`);
        }
        return match[1];
      });
  }
  if (value && typeof value === 'object' && value.node === 'Seq') {
    return (value.children || []).map((child) => extractPrim(child));
  }
  throw new Error('Unsupported flow representation');
}

function extractPrim(node) {
  if (node && node.node === 'Prim' && typeof node.prim === 'string') {
    return node.prim;
  }
  if (typeof node.prim === 'string') {
    return node.prim;
  }
  throw new Error('Unsupported IR node for flow');
}

function declareSorts(sorts = new Set()) {
  return Array.from(sorts)
    .sort()
    .map((sort) => `(declare-sort ${sort} 0)`);
}

function declareFunctions(functions = new Set()) {
  return Array.from(functions)
    .sort()
    .map((fn) => {
      const signature = FUNCTION_SIGNATURES[fn];
      if (!signature) {
        throw new Error(`Unknown function symbol: ${fn}`);
      }
      const domain = signature.domain.join(' ');
      return `(declare-fun ${fn} (${domain}) ${signature.codomain})`;
    });
}

function addAll(target, source = new Set()) {
  for (const value of source) {
    target.add(value);
  }
}
