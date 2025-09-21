const SORT_DECLS = {
  Val: '(declare-sort Val 0)',
  Bytes: '(declare-sort Bytes 0)'
};

const LAW_DEFINITIONS = {
  'idempotent:hash': {
    sorts: ['Val'],
    declarations: ['(declare-fun H (Val) Val)'],
    assertions: ['(assert (forall ((x Val)) (= (H (H x)) (H x))))']
  },
  'inverse:serialize-deserialize': {
    sorts: ['Val', 'Bytes'],
    declarations: ['(declare-fun S (Val) Bytes)', '(declare-fun D (Bytes) Val)'],
    assertions: ['(assert (forall ((v Val)) (= (D (S v)) v)))']
  },
  'commute:emit-metric-with-pure': {
    sorts: ['Val'],
    declarations: ['(declare-fun H (Val) Val)', '(declare-fun E (Val) Val)'],
    assertions: ['(assert (forall ((x Val)) (= (E (H x)) (H (E x)))))']
  }
};

const PRIMITIVES = {
  hash: {
    name: 'hash',
    symbol: 'H',
    inSort: 'Val',
    outSort: 'Val',
    declaration: '(declare-fun H (Val) Val)'
  },
  serialize: {
    name: 'serialize',
    symbol: 'S',
    inSort: 'Val',
    outSort: 'Bytes',
    declaration: '(declare-fun S (Val) Bytes)'
  },
  deserialize: {
    name: 'deserialize',
    symbol: 'D',
    inSort: 'Bytes',
    outSort: 'Val',
    declaration: '(declare-fun D (Bytes) Val)'
  },
  'emit-metric': {
    name: 'emit-metric',
    symbol: 'E',
    inSort: 'Val',
    outSort: 'Val',
    declaration: '(declare-fun E (Val) Val)'
  }
};

function pushUnique(list, value) {
  if (!list.includes(value)) {
    list.push(value);
  }
}

function normalizeLaw(law) {
  const entry = LAW_DEFINITIONS[law];
  if (!entry) {
    throw new Error(`Unknown law: ${law}`);
  }
  const sorts = [];
  const declarations = [];
  const assertions = [];
  for (const sort of entry.sorts || []) {
    if (!SORT_DECLS[sort]) {
      throw new Error(`Unknown sort "${sort}" for law ${law}`);
    }
    pushUnique(sorts, SORT_DECLS[sort]);
  }
  for (const decl of entry.declarations || []) {
    pushUnique(declarations, decl);
  }
  for (const assertion of entry.assertions || []) {
    assertions.push(assertion);
  }
  return { sorts, declarations, assertions };
}

function normalizeFlow(flow) {
  if (Array.isArray(flow)) {
    return flow;
  }
  if (typeof flow === 'string') {
    return flow
      .split('|>')
      .map((segment) => segment.trim())
      .filter(Boolean)
      .map((segment) => {
        const match = segment.match(/^[a-zA-Z0-9_-]+/);
        if (!match) {
          throw new Error(`Unable to parse flow segment: ${segment}`);
        }
        return match[0];
      });
  }
  throw new TypeError('Flow must be an array of primitive names or a pipeline string');
}

function buildFlowExpression(flow, label) {
  const ops = normalizeFlow(flow);
  const sorts = [];
  const declarations = [];
  if (ops.length === 0) {
    pushUnique(sorts, SORT_DECLS.Val);
    return {
      inputSort: 'Val',
      resultSort: 'Val',
      sorts,
      declarations,
      defines: [`(define-fun ${label} () Val input)`]
    };
  }
  const first = PRIMITIVES[ops[0]];
  if (!first) {
    throw new Error(`Unsupported primitive: ${ops[0]}`);
  }
  let currentSort = first.inSort;
  pushUnique(sorts, SORT_DECLS[currentSort]);
  pushUnique(declarations, first.declaration);
  let expr = 'input';
  for (let i = 0; i < ops.length; i += 1) {
    const name = ops[i];
    const prim = PRIMITIVES[name];
    if (!prim) {
      throw new Error(`Unsupported primitive: ${name}`);
    }
    if (prim.inSort !== currentSort) {
      throw new Error(`Type mismatch applying ${name}: expected ${prim.inSort} but have ${currentSort}`);
    }
    pushUnique(sorts, SORT_DECLS[prim.inSort]);
    pushUnique(sorts, SORT_DECLS[prim.outSort]);
    pushUnique(declarations, prim.declaration);
    expr = `(${prim.symbol} ${expr})`;
    currentSort = prim.outSort;
  }
  const defines = [`(define-fun ${label} () ${currentSort} ${expr})`];
  return {
    inputSort: first.inSort,
    resultSort: currentSort,
    sorts,
    declarations,
    defines
  };
}

export function emitLaw(law, opts = {}) {
  const { sorts, declarations, assertions } = normalizeLaw(law, opts);
  const lines = [];
  for (const sort of sorts) {
    lines.push(sort);
  }
  for (const decl of declarations) {
    lines.push(decl);
  }
  for (const assertion of assertions) {
    lines.push(assertion);
  }
  lines.push('(check-sat)');
  return lines.join('\n') + '\n';
}

export function emitFlowEquivalence(flowA, flowB, lawSet = []) {
  const requiredSorts = [];
  const requiredDecls = [];
  const assertions = [];

  for (const law of lawSet) {
    const { sorts, declarations, assertions: ax } = normalizeLaw(law);
    for (const sort of sorts) {
      pushUnique(requiredSorts, sort);
    }
    for (const decl of declarations) {
      pushUnique(requiredDecls, decl);
    }
    for (const statement of ax) {
      assertions.push(statement);
    }
  }

  const flowInfoA = buildFlowExpression(flowA, 'outA');
  const flowInfoB = buildFlowExpression(flowB, 'outB');

  if (flowInfoA.inputSort !== flowInfoB.inputSort) {
    throw new Error('Flow inputs must share the same sort to compare equivalence');
  }
  if (flowInfoA.resultSort !== flowInfoB.resultSort) {
    throw new Error('Flow outputs must share the same sort to compare equivalence');
  }

  for (const sort of flowInfoA.sorts.concat(flowInfoB.sorts)) {
    pushUnique(requiredSorts, sort);
  }
  for (const decl of flowInfoA.declarations.concat(flowInfoB.declarations)) {
    pushUnique(requiredDecls, decl);
  }

  const lines = [];
  for (const sort of requiredSorts) {
    lines.push(sort);
  }
  for (const decl of requiredDecls) {
    lines.push(decl);
  }

  const inputSortDecl = SORT_DECLS[flowInfoA.inputSort];
  if (!inputSortDecl) {
    throw new Error(`Unknown input sort: ${flowInfoA.inputSort}`);
  }
  if (!requiredSorts.includes(inputSortDecl)) {
    lines.push(inputSortDecl);
  }
  lines.push(`(declare-const input ${flowInfoA.inputSort})`);

  for (const define of flowInfoA.defines) {
    lines.push(define);
  }
  for (const define of flowInfoB.defines) {
    lines.push(define);
  }
  for (const ax of assertions) {
    lines.push(ax);
  }
  lines.push('(assert (not (= outA outB)))');
  lines.push('(check-sat)');
  return lines.join('\n') + '\n';
}
