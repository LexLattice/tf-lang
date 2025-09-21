const LAW_DEFINITIONS = new Map([
  [
    'idempotent:hash',
    {
      sorts: ['(declare-sort Val 0)'],
      decls: ['(declare-fun H (Val) Val)'],
      axioms: ['(assert (forall ((x Val)) (= (H (H x)) (H x))))']
    }
  ],
  [
    'inverse:serialize-deserialize',
    {
      sorts: ['(declare-sort Val 0)', '(declare-sort Bytes 0)'],
      decls: ['(declare-fun S (Val) Bytes)', '(declare-fun D (Bytes) Val)'],
      axioms: ['(assert (forall ((v Val)) (= (D (S v)) v)))']
    }
  ],
  [
    'commute:emit-metric-with-pure',
    {
      sorts: ['(declare-sort Val 0)'],
      decls: ['(declare-fun E (Val) Val)', '(declare-fun H (Val) Val)'],
      axioms: ['(assert (forall ((x Val)) (= (E (H x)) (H (E x)))))']
    }
  ]
]);

const SORT_DECLS = new Map([
  ['Val', '(declare-sort Val 0)'],
  ['Bytes', '(declare-sort Bytes 0)']
]);

const PRIM_DEFS = new Map([
  [
    'hash',
    {
      symbol: 'H',
      domain: ['Val'],
      range: 'Val'
    }
  ],
  [
    'serialize',
    {
      symbol: 'S',
      domain: ['Val'],
      range: 'Bytes'
    }
  ],
  [
    'deserialize',
    {
      symbol: 'D',
      domain: ['Bytes'],
      range: 'Val'
    }
  ],
  [
    'emit-metric',
    {
      symbol: 'E',
      domain: ['Val'],
      range: 'Val'
    }
  ]
]);

export function emitLaw(law, opts = {}) {
  const definition = LAW_DEFINITIONS.get(law);
  if (!definition) {
    throw new Error(`unknown law: ${law}`);
  }
  const lines = [];
  pushAllUnique(lines, definition.sorts);
  pushAllUnique(lines, definition.decls);
  pushAllUnique(lines, definition.axioms);
  lines.push('(check-sat)');
  return lines.join('\n') + '\n';
}

export function emitFlowEquivalence(irA, irB, lawSet = []) {
  const context = createContext();
  const laws = Array.isArray(lawSet) ? lawSet : [];
  for (const law of laws) {
    const definition = LAW_DEFINITIONS.get(law);
    if (!definition) {
      throw new Error(`unknown law: ${law}`);
    }
    for (const sortDecl of definition.sorts || []) {
      context.addSort(sortDecl);
    }
    for (const decl of definition.decls || []) {
      context.addDecl(decl);
    }
    for (const axiom of definition.axioms || []) {
      context.addAxiom(axiom);
    }
  }

  context.ensureSort('Val');
  const inputSymbol = 'x';
  context.addDeclaration(`(declare-const ${inputSymbol} Val)`);

  const outA = evaluateFlow(irA, inputSymbol, 'Val', context);
  const outB = evaluateFlow(irB, inputSymbol, 'Val', context);

  if (outA.sort !== outB.sort) {
    throw new Error(`flow outputs have different sorts: ${outA.sort} vs ${outB.sort}`);
  }

  const lines = [];
  lines.push(...context.sorts);
  lines.push(...context.functionDecls);
  lines.push(...context.additionalDecls);
  lines.push(...context.axioms);
  lines.push(`(define-fun outA () ${outA.sort} ${outA.term})`);
  lines.push(`(define-fun outB () ${outB.sort} ${outB.term})`);
  lines.push('(assert (not (= outA outB)))');
  lines.push('(check-sat)');
  return lines.join('\n') + '\n';
}

function createContext() {
  return {
    sorts: [],
    functionDecls: [],
    additionalDecls: [],
    axioms: [],
    seenSorts: new Set(),
    seenDecls: new Set(),
    seenAdditional: new Set(),
    seenAxioms: new Set(),
    unknownSymbols: new Map(),
    ensureSort(name) {
      const decl = SORT_DECLS.get(name);
      if (!decl) {
        throw new Error(`unknown sort: ${name}`);
      }
      this.addSort(decl);
    },
    addSort(decl) {
      if (!this.seenSorts.has(decl)) {
        this.seenSorts.add(decl);
        this.sorts.push(decl);
      }
    },
    addDecl(decl) {
      if (!this.seenDecls.has(decl)) {
        this.seenDecls.add(decl);
        this.functionDecls.push(decl);
      }
    },
    addDeclaration(decl) {
      if (!this.seenAdditional.has(decl)) {
        this.seenAdditional.add(decl);
        this.additionalDecls.push(decl);
      }
    },
    addAxiom(axiom) {
      if (!this.seenAxioms.has(axiom)) {
        this.seenAxioms.add(axiom);
        this.axioms.push(axiom);
      }
    },
    resolvePrim(name) {
      const key = typeof name === 'string' ? name.toLowerCase() : '';
      if (!key) {
        throw new Error('invalid primitive name');
      }
      if (PRIM_DEFS.has(key)) {
        const def = PRIM_DEFS.get(key);
        this.ensureSort(def.range);
        for (const sort of def.domain) {
          this.ensureSort(sort);
        }
        this.addDecl(
          `(declare-fun ${def.symbol} (${def.domain.join(' ')}) ${def.range})`
        );
        return def;
      }
      if (!this.unknownSymbols.has(key)) {
        const symbol = `F_${key.replace(/[^A-Za-z0-9]/g, '_') || 'prim'}`;
        this.unknownSymbols.set(key, symbol);
      }
      const symbol = this.unknownSymbols.get(key);
      this.ensureSort('Val');
      const decl = `(declare-fun ${symbol} (Val) Val)`;
      this.addDecl(decl);
      return { symbol, domain: ['Val'], range: 'Val' };
    }
  };
}

function evaluateFlow(ir, inputTerm, inputSort, context) {
  const primitives = collectPrimitives(ir);
  let term = inputTerm;
  let sort = inputSort;
  for (const primName of primitives) {
    const def = context.resolvePrim(primName);
    if (def.domain.length !== 1) {
      throw new Error(`unsupported arity for ${primName}`);
    }
    const expectedSort = def.domain[0];
    if (sort !== expectedSort) {
      throw new Error(`sort mismatch for ${primName}: expected ${expectedSort}, got ${sort}`);
    }
    term = `(${def.symbol} ${term})`;
    sort = def.range;
  }
  return { term, sort };
}

function collectPrimitives(node) {
  const acc = [];
  walk(node, (current) => {
    if (current?.node === 'Prim' && typeof current.prim === 'string') {
      acc.push(current.prim);
    }
  });
  return acc;
}

function walk(node, visit) {
  if (!node || typeof node !== 'object') {
    return;
  }
  visit(node);
  if (Array.isArray(node.children)) {
    for (const child of node.children) {
      walk(child, visit);
    }
  }
}

function pushAllUnique(target, values = []) {
  for (const value of values) {
    if (!target.includes(value)) {
      target.push(value);
    }
  }
}
