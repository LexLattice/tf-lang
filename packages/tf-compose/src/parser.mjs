export function parseDSL(src) {
  const tokens = tokenize(src);
  const seq = parseSeq(tokens);
  expectEOF(tokens);
  return seq;
}

function tokenize(src) {
  const lines = src.split(/\r?\n/);
  const list = [];
  let i = 0;
  let line = 1;
  let col = 1;

  function pos() {
    return { index: i, line, col };
  }
  function advanceOne() {
    const ch = src[i];
    i++;
    if (ch === '\r') {
      if (src[i] === '\n') i++;
      line++;
      col = 1;
    } else if (ch === '\n') {
      line++;
      col = 1;
    } else {
      col++;
    }
  }

  function advanceN(n) {
    for (let k = 0; k < n; k++) advanceOne();
  }

  function pushToken(t, start, end, value) {
    list.push({ t, v: value, start, end });
  }

  function lexError(position, message, span = 2) {
    throw new Error(formatError(src, lines, position, message, span));
  }

  const numberRegex = /-?(?:0|[1-9]\d*)(?:\.\d+)?(?:[eE][+-]?\d+)?/y;
  while (i < src.length) {
    const ch = src[i];
    if (/\s/.test(ch)) { advanceOne(); continue; }

    if (src.startsWith('|>', i)) {
      const start = pos();
      advanceN(2);
      pushToken('PIPE', start, pos());
      continue;
    }
    if (src.startsWith('par{', i)) {
      const start = pos();
      advanceN(4);
      pushToken('PAR_OPEN', start, pos());
      continue;
    }
    if (src.startsWith('seq{', i)) {
      const start = pos();
      advanceN(4);
      pushToken('SEQ_OPEN', start, pos());
      continue;
    }
    const afterAuthorize = src[i + 9] ?? '';
    if (src.startsWith('authorize', i) && (afterAuthorize === '{' || afterAuthorize === '(')) {
      const start = pos();
      advanceN(9);
      pushToken('REGION_AUTH', start, pos());
      continue;
    }
    const afterTxn = src[i + 3] ?? '';
    if (src.startsWith('txn', i) && (afterTxn === '{' || afterTxn === '(')) {
      const start = pos();
      advanceN(3);
      pushToken('REGION_TXN', start, pos());
      continue;
    }

    const simpleTokens = {
      '{': 'LBRACE',
      '}': 'RBRACE',
      '(': 'LPAREN',
      ')': 'RPAREN',
      ';': 'SEMI',
      ',': 'COMMA',
      '=': 'EQ',
      '[': 'LBRACKET',
      ']': 'RBRACKET',
      ':': 'COLON',
    };
    if (simpleTokens[ch]) {
      const start = pos();
      advanceOne();
      pushToken(simpleTokens[ch], start, pos());
      continue;
    }
    if (ch === '"' || ch === "'") {
      const quote = ch;
      const start = pos();
      advanceOne();
      let value = '';
      let closed = false;
      while (i < src.length) {
        const c = src[i];
        if (c === quote) { closed = true; advanceOne(); break; }
        if (c === '\\') {
          advanceOne();
          if (i >= src.length) lexError(start, 'Unterminated string literal');
          const escaped = src[i];
          advanceOne();
          value += escaped;
        } else if (c === '\n' || c === '\r') {
          lexError(pos(), 'Unexpected newline in string literal');
        } else {
          value += c;
          advanceOne();
        }
      }
      if (!closed) {
        lexError(start, 'Unterminated string literal');
      }
      pushToken('STRING', start, pos(), value);
      continue;
    }
    const nextChar = src[i + 1] ?? '';
    if ((ch === '-' && /[0-9.]/.test(nextChar)) || /[0-9]/.test(ch)) {
      numberRegex.lastIndex = i;
      const match = numberRegex.exec(src);
      if (!match) {
        lexError(pos(), 'Invalid number literal');
      }
      const raw = match[0];
      const start = pos();
      advanceN(raw.length);
      pushToken('NUMBER', start, pos(), Number(raw));
      continue;
    }

    if (/[A-Za-z_]/.test(ch)) {
      const start = pos();
      let j = i;
      while (j < src.length && /[A-Za-z0-9_\-.]/.test(src[j])) j++;
      const text = src.slice(i, j);
      advanceN(j - i);
      pushToken('IDENT', start, pos(), text);
      continue;
    }

    if (ch === '-' || ch === '.') {
      const start = pos();
      let j = i;
      while (j < src.length && /[A-Za-z0-9_\-.]/.test(src[j])) j++;
      if (j > i) {
        const text = src.slice(i, j);
        advanceN(j - i);
        pushToken('IDENT', start, pos(), text);
        continue;
      }
    }

    lexError(pos(), 'Unexpected character ' + JSON.stringify(ch));
  }

  return { src, lines, list, i: 0, eof: pos() };
}
function peek(tokens) {
  return tokens.list[tokens.i] || { t: 'EOF', start: tokens.eof, end: tokens.eof };
}

function tokenLabel(kind, value) {
  switch (kind) {
    case 'PIPE': return '|>';
    case 'PAR_OPEN': return 'par{';
    case 'SEQ_OPEN': return 'seq{';
    case 'REGION_AUTH': return 'authorize';
    case 'REGION_TXN': return 'txn';
    case 'LBRACE': return '{';
    case 'RBRACE': return '}';
    case 'LPAREN': return '(';
    case 'RPAREN': return ')';
    case 'SEMI': return ';';
    case 'COMMA': return ',';
    case 'EQ': return '=';
    case 'LBRACKET': return '[';
    case 'RBRACKET': return ']';
    case 'COLON': return ':';
    case 'STRING': return 'string';
    case 'NUMBER': return 'number';
    case 'IDENT': return value ? 'identifier ' + JSON.stringify(value) : 'identifier';
    case 'EOF': return 'end of input';
    default: return kind;
  }
}
function take(tokens, kind, message) {
  const token = peek(tokens);
  if (token.t !== kind) {
    const got = tokenLabel(token.t, token.v);
    const expected = tokenLabel(kind);
    throw new Error(formatError(tokens.src, tokens.lines, token.start || tokens.eof, message || ('Expected ' + expected + ', got ' + got), spanLength(token)));
  }
  tokens.i++;
  return token;
}

function maybe(tokens, kind) {
  const token = peek(tokens);
  if (token.t === kind) {
    tokens.i++;
    return true;
  }
  return false;
}

function expectEOF(tokens) {
  const token = peek(tokens);
  if (token.t !== 'EOF') {
    throw new Error(formatError(tokens.src, tokens.lines, token.start, 'Unexpected ' + tokenLabel(token.t, token.v), spanLength(token)));
  }
}
function parseSeq(tokens) {
  const parts = [parseStep(tokens)];
  while (maybe(tokens, 'PIPE')) parts.push(parseStep(tokens));
  return parts.length === 1 ? parts[0] : { node: 'Seq', children: parts };
}

function parseBlock(tokens, node) {
  const children = [];
  while (true) {
    children.push(parseStep(tokens));
    if (maybe(tokens, 'SEMI')) continue;
    take(tokens, 'RBRACE');
    break;
  }
  node.children = children;
  return node;
}
function parseRegion(tokens, kind) {
  const attrs = {};
  if (maybe(tokens, 'LPAREN')) {
    if (!maybe(tokens, 'RPAREN')) {
      while (true) {
        const keyTok = take(tokens, 'IDENT');
        take(tokens, 'EQ');
        attrs[keyTok.v] = parseLiteral(tokens);
        if (maybe(tokens, 'COMMA')) continue;
        take(tokens, 'RPAREN');
        break;
      }
    }
  }
  take(tokens, 'LBRACE');
  return parseBlock(tokens, { node: 'Region', kind, attrs, children: [] });
}

function parseStep(tokens) {
  if (maybe(tokens, 'PAR_OPEN')) return parseBlock(tokens, { node: 'Par', children: [] });
  if (maybe(tokens, 'SEQ_OPEN')) return parseBlock(tokens, { node: 'Seq', children: [] });
  if (maybe(tokens, 'REGION_AUTH')) return parseRegion(tokens, 'Authorize');
  if (maybe(tokens, 'REGION_TXN')) return parseRegion(tokens, 'Transaction');
  const idTok = take(tokens, 'IDENT');
  const id = idTok.v;
  const args = {};
  if (maybe(tokens, 'LPAREN')) {
    if (!maybe(tokens, 'RPAREN')) {
      while (true) {
        const keyTok = take(tokens, 'IDENT');
        take(tokens, 'EQ');
        args[keyTok.v] = parseLiteral(tokens);
        if (maybe(tokens, 'COMMA')) continue;
        take(tokens, 'RPAREN');
        break;
      }
    }
  }
  return { node: 'Prim', prim: id.toLowerCase(), args };
}
function parseLiteral(tokens) {
  const token = peek(tokens);
  switch (token.t) {
    case 'STRING':
      tokens.i++;
      return token.v;
    case 'NUMBER':
      tokens.i++;
      return token.v;
    case 'IDENT':
      tokens.i++;
      if (token.v === 'true') return true;
      if (token.v === 'false') return false;
      if (token.v === 'null') return null;
      return token.v;
    case 'LBRACKET':
      return parseArrayLiteral(tokens);
    case 'LBRACE':
      return parseObjectLiteral(tokens);
    default:
      throw new Error(formatError(tokens.src, tokens.lines, token.start || tokens.eof, 'Expected literal', spanLength(token)));
  }
}
function parseArrayLiteral(tokens) {
  take(tokens, 'LBRACKET');
  const arr = [];
  if (maybe(tokens, 'RBRACKET')) return arr;
  while (true) {
    arr.push(parseLiteral(tokens));
    if (maybe(tokens, 'COMMA')) {
      if (maybe(tokens, 'RBRACKET')) break;
      continue;
    }
    take(tokens, 'RBRACKET');
    break;
  }
  return arr;
}
function parseObjectLiteral(tokens) {
  take(tokens, 'LBRACE');
  const obj = {};
  if (maybe(tokens, 'RBRACE')) return obj;
  while (true) {
    const keyTok = peek(tokens);
    let key;
    if (keyTok.t === 'STRING') {
      tokens.i++;
      key = keyTok.v;
    } else if (keyTok.t === 'IDENT') {
      tokens.i++;
      key = keyTok.v;
    } else {
      throw new Error(formatError(tokens.src, tokens.lines, keyTok.start || tokens.eof, 'Expected object key', spanLength(keyTok)));
    }
    take(tokens, 'COLON');
    obj[key] = parseLiteral(tokens);
    if (maybe(tokens, 'COMMA')) {
      if (maybe(tokens, 'RBRACE')) break;
      continue;
    }
    take(tokens, 'RBRACE');
    break;
  }
  return obj;
}
function spanLength(token) {
  if (!token || !token.start || !token.end) return 2;
  const length = Math.max(token.end.index - token.start.index, 1);
  return Math.max(2, Math.min(length, 12));
}

function formatError(src, lines, position, message, span = 2) {
  const lineNum = position && position.line ? position.line : 1;
  const colNum = position && position.col ? position.col : 1;
  const safeLine = lineNum < 1 ? 1 : lineNum;
  const lineText = lines[safeLine - 1] ?? '';
  const available = Math.max(lineText.length - (colNum - 1), 1);
  const pointerWidth = Math.max(2, Math.min(span, 12, available));
  const caretLine = ' '.repeat(Math.max(colNum - 1, 0)) + '^'.repeat(pointerWidth);
  return message + ' at ' + safeLine + ':' + colNum + '\n' + lineText + '\n' + caretLine;
}
