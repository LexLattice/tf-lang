// DSL parser (extended) supporting regions: authorize{ ... } and txn{ ... }
export function parseDSL(src) {
  const tokens = tokenize(src);
  const seq = parseSeq(tokens);
  while (maybe(tokens, 'SEMI')) {
    // allow optional trailing semicolons at the top level
  }
  expectEOF(tokens);
  return annotateLetRefs(seq);
}

const RESERVED_BINDING_NAMES = new Set(['let', 'include', 'seq', 'par', 'authorize', 'txn']);

function tokenize(src) {
  const tokens = [];
  let i = 0;
  let line = 1;
  let col = 1;

  function currentPos() {
    return { index: i, line, col };
  }

  function advanceChar() {
    const ch = src[i++];
    if (ch === '\n') {
      line += 1;
      col = 1;
    } else if (ch === '\r') {
      if (src[i] === '\n') {
        i += 1;
      }
      line += 1;
      col = 1;
    } else {
      col += 1;
    }
    return ch;
  }

  function makeToken(t, v, start) {
    return { t, v, start, end: currentPos() };
  }

  function throwError(start, message, span = 2) {
    throw syntaxErrorFromPositions(src, start, currentPos(), message, span);
  }

  function consumeWord(word) {
    for (const ch of word) {
      if (src[i] !== ch) return false;
      advanceChar();
    }
    return true;
  }

  function consumeWhile(regex) {
    let consumed = '';
    while (i < src.length && regex.test(src[i])) {
      consumed += advanceChar();
    }
    return consumed;
  }

  while (i < src.length) {
    const ch = src[i];
    if (/\s/.test(ch)) {
      advanceChar();
      continue;
    }

    const start = currentPos();

    if (src.startsWith('|>', i)) {
      advanceChar();
      advanceChar();
      tokens.push(makeToken('PIPE', null, start));
      continue;
    }

    if (src.startsWith('par{', i)) {
      consumeWord('par{');
      tokens.push(makeToken('PAR_OPEN', null, start));
      continue;
    }

    if (src.startsWith('seq{', i)) {
      consumeWord('seq{');
      tokens.push(makeToken('SEQ_OPEN', null, start));
      continue;
    }

    if (src.startsWith('authorize', i)) {
      let lookahead = i + 9;
      while (lookahead < src.length && /\s/.test(src[lookahead])) {
        lookahead += 1;
      }
      const next = src[lookahead] ?? '';
      if (next === '{' || next === '(') {
        consumeWord('authorize');
        tokens.push(makeToken('REGION_AUTH', null, start));
        continue;
      }
    }

    if (src.startsWith('txn', i)) {
      const next = src[i + 3] ?? '';
      if (next === '{' || next === '(') {
        consumeWord('txn');
        tokens.push(makeToken('REGION_TXN', null, start));
        continue;
      }
    }

    if (ch === '{') {
      advanceChar();
      tokens.push(makeToken('LBRACE', null, start));
      continue;
    }

    if (ch === '}') {
      advanceChar();
      tokens.push(makeToken('RBRACE', null, start));
      continue;
    }

    if (ch === '[') {
      advanceChar();
      tokens.push(makeToken('LBRACKET', null, start));
      continue;
    }

    if (ch === ']') {
      advanceChar();
      tokens.push(makeToken('RBRACKET', null, start));
      continue;
    }

    if (ch === '(') {
      advanceChar();
      tokens.push(makeToken('LPAREN', null, start));
      continue;
    }

    if (ch === ')') {
      advanceChar();
      tokens.push(makeToken('RPAREN', null, start));
      continue;
    }

    if (ch === ';') {
      advanceChar();
      tokens.push(makeToken('SEMI', null, start));
      continue;
    }

    if (ch === ',') {
      advanceChar();
      tokens.push(makeToken('COMMA', null, start));
      continue;
    }

    if (ch === '=') {
      advanceChar();
      tokens.push(makeToken('EQ', null, start));
      continue;
    }

    if (ch === ':') {
      advanceChar();
      tokens.push(makeToken('COLON', null, start));
      continue;
    }

    if (ch === '"' || ch === "'") {
      const quote = advanceChar();
      let buf = '';
      let closed = false;
      while (i < src.length) {
        const nextCh = advanceChar();
        if (nextCh === quote) {
          closed = true;
          break;
        }
        if (nextCh === '\\') {
          if (i >= src.length) {
            throwError(start, 'Unterminated string literal');
          }
          const escaped = advanceChar();
          buf += escaped;
          continue;
        }
        buf += nextCh;
      }
      if (!closed) {
        throwError(start, 'Unterminated string literal');
      }
      tokens.push(makeToken('STRING', buf, start));
      continue;
    }

    const isNumberStart = (ch === '-' && /[0-9]/.test(src[i + 1] ?? '')) || /[0-9]/.test(ch);
    if (isNumberStart) {
      let raw = '';
      if (ch === '-') {
        raw += advanceChar();
      }
      const digits = consumeWhile(/[0-9]/);
      raw += digits;
      if (!digits) {
        throwError(start, 'Invalid number literal');
      }
      if (src[i] === '.') {
        raw += advanceChar();
        const frac = consumeWhile(/[0-9]/);
        if (!frac) {
          throwError(start, 'Invalid number literal');
        }
        raw += frac;
      }
      const value = Number(raw);
      if (!Number.isFinite(value)) {
        throwError(start, 'Invalid number literal');
      }
      tokens.push(makeToken('NUMBER', value, start));
      continue;
    }

    let ident = '';
    while (i < src.length && /[A-Za-z0-9_\-\.]/.test(src[i])) {
      ident += advanceChar();
    }
    if (ident) {
      if (ident === 'let') {
        tokens.push(makeToken('LET', ident, start));
        continue;
      }
      if (ident === 'include') {
        tokens.push(makeToken('INCLUDE', ident, start));
        continue;
      }
      tokens.push(makeToken('IDENT', ident, start));
      continue;
    }

    throwError(start, `Unexpected character '${ch}'`);
  }

  return { i: 0, list: tokens, src, endPos: { index: i, line, col } };
}

function peek(tokens) {
  return tokens.list[tokens.i] || { t: 'EOF', start: tokens.endPos, end: tokens.endPos };
}

function take(tokens, kind) {
  const token = peek(tokens);
  if (token.t !== kind) {
    throw syntaxError(tokens, token, `Expected ${kind}, got ${token.t}`);
  }
  tokens.i += 1;
  return token;
}

function maybe(tokens, kind) {
  const token = peek(tokens);
  if (token.t === kind) {
    tokens.i += 1;
    return true;
  }
  return false;
}

function expectEOF(tokens) {
  if (peek(tokens).t !== 'EOF') {
    throw syntaxError(tokens, peek(tokens), 'Trailing tokens');
  }
}

function syntaxError(tokens, token, message, span) {
  const start = token.start || tokens.endPos;
  const end = token.end || start;
  const err = new Error(formatErrorMessage(tokens.src, start, end, message, span));
  err.loc = { line: start.line, col: start.col };
  return err;
}

function syntaxErrorFromPositions(src, start, end, message, span) {
  return new Error(formatErrorMessage(src, start, end, message, span));
}

function formatErrorMessage(src, start, end, message, spanOverride) {
  const line = start.line ?? 1;
  const col = start.col ?? 1;
  const index = start.index ?? 0;
  const span = spanOverride ?? Math.max(1, (end?.index ?? index + 1) - index);
  const caretCount = Math.min(12, Math.max(2, span));

  let lineStart = index;
  while (lineStart > 0 && src[lineStart - 1] !== '\n') {
    lineStart -= 1;
  }
  let lineEnd = index;
  while (lineEnd < src.length && src[lineEnd] !== '\n') {
    lineEnd += 1;
  }
  const lineText = src.slice(lineStart, lineEnd);
  const caretOffset = Math.max(0, index - lineStart);
  const caretLine = `${' '.repeat(caretOffset)}${'^'.repeat(caretCount)}`;

  return `Parse error at ${line}:${col}: ${message}\n${lineText}\n${caretLine}`;
}

function parseSeq(tokens) {
  const first = parseStep(tokens);
  if (!maybe(tokens, 'PIPE')) {
    return first;
  }
  if (isBindingNode(first)) {
    throw syntaxError(tokens, peek(tokens), 'Let/include cannot be used in pipelines');
  }
  const parts = [first, parseStep(tokens)];
  while (maybe(tokens, 'PIPE')) {
    parts.push(parseStep(tokens));
  }
  return { node: 'Seq', children: parts };
}

function parseBlock(tokens, node) {
  const kids = [];
  if (maybe(tokens, 'RBRACE')) {
    node.children = kids;
    return node;
  }
  while (true) {
    kids.push(parseSeq(tokens));
    if (maybe(tokens, 'SEMI')) {
      if (maybe(tokens, 'RBRACE')) break;
      continue;
    }
    take(tokens, 'RBRACE');
    break;
  }
  node.children = kids;
  return node;
}

function parseRegion(tokens, kind) {
  const attrs = {};
  if (maybe(tokens, 'LPAREN')) {
    if (!maybe(tokens, 'RPAREN')) {
      while (true) {
        const key = take(tokens, 'IDENT').v;
        take(tokens, 'EQ');
        attrs[key] = parseValue(tokens);
        if (maybe(tokens, 'COMMA')) {
          if (maybe(tokens, 'RPAREN')) break;
          continue;
        }
        take(tokens, 'RPAREN');
        break;
      }
    }
  }
  take(tokens, 'LBRACE');
  return parseBlock(tokens, { node: 'Region', kind, attrs, children: [] });
}

function parseArgs(tokens) {
  const args = {};
  if (!maybe(tokens, 'LPAREN')) return args;
  if (maybe(tokens, 'RPAREN')) return args;
  while (true) {
    const key = take(tokens, 'IDENT').v;
    take(tokens, 'EQ');
    args[key] = parseValue(tokens);
    if (maybe(tokens, 'COMMA')) {
      if (maybe(tokens, 'RPAREN')) break;
      continue;
    }
    take(tokens, 'RPAREN');
    break;
  }
  return args;
}

function parseStep(tokens) {
  const token = peek(tokens);
  if (token.t === 'LET') {
    tokens.i += 1;
    return parseLet(tokens, token);
  }
  if (token.t === 'INCLUDE') {
    tokens.i += 1;
    return parseInclude(tokens, token);
  }
  if (maybe(tokens, 'PAR_OPEN')) return parseBlock(tokens, { node: 'Par', children: [] });
  if (maybe(tokens, 'SEQ_OPEN')) return parseBlock(tokens, { node: 'Seq', syntax: 'block', children: [] });
  if (maybe(tokens, 'REGION_AUTH')) return parseRegion(tokens, 'Authorize');
  if (maybe(tokens, 'REGION_TXN')) return parseRegion(tokens, 'Transaction');
  const id = take(tokens, 'IDENT');
  const args = parseArgs(tokens);
  return {
    node: 'Prim',
    prim: id.v.toLowerCase(),
    raw: id.v,
    args
  };
}

function parseLet(tokens, letToken) {
  const nameToken = take(tokens, 'IDENT');
  if (RESERVED_BINDING_NAMES.has(nameToken.v.toLowerCase())) {
    throw syntaxError(tokens, nameToken, `Reserved keyword '${nameToken.v}' cannot be used as a binding name`);
  }
  take(tokens, 'EQ');
  const init = parseSeq(tokens);
  const last = lastConsumedToken(tokens) || nameToken;
  return {
    node: 'Let',
    name: nameToken.v,
    init,
    body: null,
    loc: makeLoc(letToken.start, last.end),
  };
}

function parseInclude(tokens, includeToken) {
  const pathToken = take(tokens, 'STRING');
  return {
    node: 'Include',
    path: pathToken.v,
    loc: makeLoc(includeToken.start, pathToken.end),
  };
}

function parseValue(tokens) {
  const token = peek(tokens);
  if (token.t === 'STRING') {
    tokens.i += 1;
    return token.v;
  }
  if (token.t === 'NUMBER') {
    tokens.i += 1;
    return token.v;
  }
  if (token.t === 'IDENT') {
    tokens.i += 1;
    if (token.v === 'true') return true;
    if (token.v === 'false') return false;
    if (token.v === 'null') return null;
    return token.v;
  }
  if (token.t === 'LBRACKET') {
    return parseArray(tokens);
  }
  if (token.t === 'LBRACE') {
    return parseObject(tokens);
  }
  throw syntaxError(tokens, token, 'Unexpected value');
}

function parseArray(tokens) {
  take(tokens, 'LBRACKET');
  const values = [];
  if (maybe(tokens, 'RBRACKET')) return values;
  while (true) {
    values.push(parseValue(tokens));
    if (maybe(tokens, 'COMMA')) {
      if (maybe(tokens, 'RBRACKET')) break;
      continue;
    }
    take(tokens, 'RBRACKET');
    break;
  }
  return values;
}

function parseObject(tokens) {
  take(tokens, 'LBRACE');
  const obj = Object.create(null);
  if (maybe(tokens, 'RBRACE')) return obj;
  while (true) {
    const keyTok = peek(tokens);
    let key;
    if (keyTok.t === 'STRING') {
      key = take(tokens, 'STRING').v;
    } else if (keyTok.t === 'IDENT') {
      key = take(tokens, 'IDENT').v;
    } else if (keyTok.t === 'NUMBER') {
      key = String(take(tokens, 'NUMBER').v);
    } else {
      throw syntaxError(tokens, keyTok, 'Expected string, identifier, or number key');
    }
    take(tokens, 'COLON');
    obj[key] = parseValue(tokens);
    if (maybe(tokens, 'COMMA')) {
      if (maybe(tokens, 'RBRACE')) break;
      continue;
    }
    take(tokens, 'RBRACE');
    break;
  }
  return obj;
}

function isBindingNode(node) {
  return node && typeof node === 'object' && (node.node === 'Let' || node.node === 'Include');
}

function lastConsumedToken(tokens) {
  const idx = tokens.i - 1;
  return idx >= 0 ? tokens.list[idx] || null : null;
}

function makeLoc(start, end) {
  return { start: clonePos(start), end: clonePos(end) };
}

function clonePos(pos) {
  return pos ? { index: pos.index, line: pos.line, col: pos.col } : null;
}

function annotateLetRefs(root) {
  const envStack = [new Map()];
  return annotateNode(root, envStack);
}

function annotateNode(node, envStack) {
  if (!node || typeof node !== 'object') return node;

  if (node.node === 'Let') {
    if (node.init) {
      node.init = annotateNode(node.init, envStack);
    }
    bindLetName(envStack, node.name);
    if (node.body) {
      node.body = annotateNode(node.body, envStack);
    }
    return node;
  }

  if (node.node === 'Seq') {
    const isBlock = node.syntax === 'block';
    if (isBlock) pushScope(envStack);
    const kids = node.children ?? [];
    node.children = kids.map((child) => annotateNode(child, envStack));
    if (isBlock) popScope(envStack);
    return node;
  }

  if (node.node === 'Par') {
    const children = node.children ?? [];
    node.children = children.map((child) => annotateNode(child, cloneEnvStack(envStack)));
    return node;
  }

  if (node.node === 'Region') {
    pushScope(envStack);
    node.children = (node.children ?? []).map((child) => annotateNode(child, envStack));
    popScope(envStack);
    return node;
  }

  if (Array.isArray(node.children)) {
    node.children = node.children.map((child) => annotateNode(child, envStack));
    return node;
  }

  if (node.node === 'Prim' && isRefCandidate(node, envStack)) {
    return {
      node: 'Ref',
      name: node.raw || node.prim,
      loc: node.loc
    };
  }

  return node;
}

function isRefCandidate(node, envStack) {
  if (!node || typeof node !== 'object') return false;
  const hasArgs = node.args && Object.keys(node.args).length > 0;
  if (hasArgs) return false;
  const key = normalizeBindingKey(node.prim);
  return lookupLetName(envStack, key);
}

function bindLetName(envStack, name) {
  const top = envStack[envStack.length - 1];
  top.set(normalizeBindingKey(name), true);
}

function lookupLetName(envStack, key) {
  for (let i = envStack.length - 1; i >= 0; i -= 1) {
    if (envStack[i].has(key)) return true;
  }
  return false;
}

function normalizeBindingKey(name) {
  return typeof name === 'string' ? name.toLowerCase() : '';
}

function pushScope(envStack) {
  envStack.push(new Map());
}

function popScope(envStack) {
  envStack.pop();
}

function cloneEnvStack(envStack) {
  return envStack.map((frame) => new Map(frame));
}
