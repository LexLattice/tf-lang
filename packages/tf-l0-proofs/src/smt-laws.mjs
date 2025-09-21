const SORTS = {
  Val: { arity: 0 },
  Bytes: { arity: 0 },
};

const FUNCTIONS = {
  H: { domain: ['Val'], codomain: 'Val' },
  S: { domain: ['Val'], codomain: 'Bytes' },
  D: { domain: ['Bytes'], codomain: 'Val' },
  E: { domain: ['Val'], codomain: 'Val' },
};

const LAW_DEFINITIONS = {
  'idempotent:hash': {
    sorts: ['Val'],
    functions: ['H'],
    axioms: ['(assert (forall ((x Val)) (= (H (H x)) (H x))))'],
  },
  'inverse:serialize-deserialize': {
    sorts: ['Val', 'Bytes'],
    functions: ['S', 'D'],
    axioms: ['(assert (forall ((v Val)) (= (D (S v)) v)))'],
  },
  'commute:emit-metric-with-pure': {
    sorts: ['Val'],
    functions: ['E', 'H'],
    axioms: ['(assert (forall ((x Val)) (= (E (H x)) (H (E x)))))'],
  },
};

const OPERATION_DEFINITIONS = {
  hash: { symbol: 'H', domain: 'Val', codomain: 'Val' },
  serialize: { symbol: 'S', domain: 'Val', codomain: 'Bytes' },
  deserialize: { symbol: 'D', domain: 'Bytes', codomain: 'Val' },
  'emit-metric': { symbol: 'E', domain: 'Val', codomain: 'Val' },
};

export function emitLaw(law, opts = {}) {
  const definition = LAW_DEFINITIONS[law];
  if (!definition) {
    throw new Error(`Unknown law: ${law}`);
  }
  const sorts = collectSorts(definition.sorts || []);
  const functions = collectFunctions(definition.functions || []);
  const body = [];
  body.push(...emitSorts(sorts));
  body.push(...emitFunctions(functions));
  body.push(...definition.axioms);
  body.push('(check-sat)');
  return body.join('\n') + '\n';
}

export function emitFlowEquivalence(flowA, flowB, lawSet = []) {
  const laws = normalizeLawList(lawSet);
  const definitionList = laws.map((name) => {
    const definition = LAW_DEFINITIONS[name];
    if (!definition) {
      throw new Error(`Unknown law: ${name}`);
    }
    return definition;
  });

  const a = analyzeFlow(flowA);
  const b = analyzeFlow(flowB);

  if (a.startSort !== b.startSort) {
    throw new Error(
      `Flow domains must match (got ${a.startSort ?? 'unknown'} vs ${
        b.startSort ?? 'unknown'
      })`
    );
  }
  if (a.endSort !== b.endSort) {
    throw new Error(
      `Flow codomains must match (got ${a.endSort ?? 'unknown'} vs ${
        b.endSort ?? 'unknown'
      })`
    );
  }

  const sorts = new Set();
  const functions = new Set();
  for (const def of definitionList) {
    for (const sort of def.sorts || []) {
      sorts.add(sort);
    }
    for (const fn of def.functions || []) {
      functions.add(fn);
    }
  }
  for (const sort of a.sorts) {
    sorts.add(sort);
  }
  for (const sort of b.sorts) {
    sorts.add(sort);
  }
  for (const fn of a.functions) {
    functions.add(fn);
  }
  for (const fn of b.functions) {
    functions.add(fn);
  }

  const body = [];
  body.push(...emitSorts(sorts));
  body.push(...emitFunctions(functions));

  const inputName = 'x';
  body.push(`(declare-const ${inputName} ${a.startSort ?? 'Val'})`);

  for (const name of laws) {
    const definition = LAW_DEFINITIONS[name];
    body.push(...definition.axioms);
  }

  body.push(`(define-fun outA () ${a.endSort ?? 'Val'} ${a.expression(inputName)})`);
  body.push(`(define-fun outB () ${b.endSort ?? 'Val'} ${b.expression(inputName)})`);
  body.push('(assert (not (= outA outB)))');
  body.push('(check-sat)');
  return body.join('\n') + '\n';
}

function analyzeFlow(flow) {
  if (!Array.isArray(flow)) {
    throw new Error('Flow must be an array of operation names');
  }
  const operations = flow
    .map((entry) => normalizeOperation(entry))
    .filter((name) => name.length > 0);
  let startSort = null;
  let currentSort = null;
  const sorts = new Set();
  const functions = new Set();
  const steps = [];

  for (const opName of operations) {
    const op = OPERATION_DEFINITIONS[opName];
    if (!op) {
      throw new Error(`Unknown operation: ${opName}`);
    }
    if (startSort === null) {
      startSort = op.domain;
      currentSort = op.domain;
      sorts.add(op.domain);
    }
    if (currentSort !== op.domain) {
      throw new Error(
        `Operation ${opName} expects ${op.domain} but received ${currentSort}`
      );
    }
    functions.add(op.symbol);
    sorts.add(op.codomain);
    steps.push(op.symbol);
    currentSort = op.codomain;
  }

  if (startSort === null) {
    startSort = 'Val';
    currentSort = 'Val';
    sorts.add('Val');
  }

  return {
    startSort,
    endSort: currentSort,
    sorts,
    functions,
    expression(inputName) {
      let expr = inputName;
      for (const symbol of steps) {
        expr = `(${symbol} ${expr})`;
      }
      return expr;
    },
  };
}

function normalizeOperation(entry) {
  if (typeof entry === 'string') {
    const trimmed = entry.trim();
    if (trimmed.length === 0) {
      return '';
    }
    const hashIndex = trimmed.indexOf('#');
    const segment = hashIndex >= 0 ? trimmed.slice(0, hashIndex).trim() : trimmed;
    if (segment.length === 0) {
      return '';
    }
    const parenIndex = segment.indexOf('(');
    const withoutArgs = parenIndex >= 0 ? segment.slice(0, parenIndex) : segment;
    const spaceIndex = withoutArgs.indexOf(' ');
    const base = spaceIndex >= 0 ? withoutArgs.slice(0, spaceIndex) : withoutArgs;
    return base.trim().toLowerCase();
  }
  throw new Error('Operation names must be strings');
}

function normalizeLawList(value) {
  if (!value) {
    return [];
  }
  if (typeof value === 'string') {
    return [value];
  }
  const list = Array.from(value);
  const seen = new Set();
  const result = [];
  for (const law of list) {
    if (typeof law !== 'string') {
      throw new Error('Law names must be strings');
    }
    if (seen.has(law)) {
      continue;
    }
    seen.add(law);
    result.push(law);
  }
  result.sort();
  return result;
}

function collectSorts(names) {
  const unique = new Set(names || []);
  const result = [];
  for (const name of unique) {
    if (!(name in SORTS)) {
      throw new Error(`Unknown sort: ${name}`);
    }
    result.push(name);
  }
  result.sort();
  return result;
}

function collectFunctions(names) {
  const unique = new Set(names || []);
  const result = [];
  for (const name of unique) {
    if (!(name in FUNCTIONS)) {
      throw new Error(`Unknown function: ${name}`);
    }
    result.push(name);
  }
  result.sort();
  return result;
}

function emitSorts(sorts) {
  const lines = [];
  const list = Array.isArray(sorts) ? sorts : Array.from(sorts);
  list.sort();
  for (const name of list) {
    const sort = SORTS[name];
    if (!sort) {
      throw new Error(`Unknown sort: ${name}`);
    }
    lines.push(`(declare-sort ${name} ${sort.arity})`);
  }
  return lines;
}

function emitFunctions(functions) {
  const lines = [];
  const list = Array.isArray(functions) ? functions : Array.from(functions);
  list.sort();
  for (const name of list) {
    const fn = FUNCTIONS[name];
    if (!fn) {
      throw new Error(`Unknown function: ${name}`);
    }
    lines.push(`(declare-fun ${name} (${fn.domain.join(' ')}) ${fn.codomain})`);
  }
  return lines;
}
