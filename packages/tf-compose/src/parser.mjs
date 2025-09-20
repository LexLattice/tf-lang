// DSL parser (extended) supporting regions: authorize{ ... } and txn{ ... }
export function parseDSL(src) {
  const tokens = tokenize(src);
  const stream = new TokenStream(tokens, src);
  const seq = parseSeq(stream);
  stream.take('EOF');
  return seq;
}

function tokenize(src) {
  const tokens = [];
  let i = 0;
  let line = 1;
  let col = 1;

  function currentPos() {
    return { index: i, line, col };
  }

  function advance() {
    const ch = src[i++];
    if (ch === '\n') {
      line += 1;
      col = 1;
    } else {
      col += 1;
    }
    return ch;
  }

  function advanceN(n) {
    for (let k = 0; k < n; k++) advance();
  }

  function addToken(t, v, start) {
    tokens.push({ t, v, start, end: currentPos() });
  }

  function error(message, start, end = currentPos()) {
    throw syntaxError(src, message, start, end);
  }

  const isIdentChar = (ch) => /[A-Za-z0-9_.-]/.test(ch);
  const isDigit = (ch) => /[0-9]/.test(ch);

  while (i < src.length) {
    const ch = src[i];
    if (ch === '\r') { advance(); continue; }
    if (/\s/.test(ch)) { advance(); continue; }

    const start = currentPos();

    if (src.startsWith('|>', i)) {
      advanceN(2);
      addToken('PIPE', null, start);
      continue;
    }
    if (src.startsWith('par{', i)) {
      advanceN(4);
      addToken('PAR_OPEN', null, start);
      continue;
    }
    if (src.startsWith('seq{', i)) {
      advanceN(4);
      addToken('SEQ_OPEN', null, start);
      continue;
    }
    if (src.startsWith('authorize', i) && (src[i + 9] === '{' || src[i + 9] === '(')) {
      advanceN(9);
      addToken('REGION_AUTH', null, start);
      continue;
    }
    if (src.startsWith('txn', i) && (src[i + 3] === '{' || src[i + 3] === '(')) {
      advanceN(3);
      addToken('REGION_TXN', null, start);
      continue;
    }
    if (ch === '{') { advance(); addToken('LBRACE', null, start); continue; }
    if (ch === '}') { advance(); addToken('RBRACE', null, start); continue; }
    if (ch === '(') { advance(); addToken('LPAREN', null, start); continue; }
    if (ch === ')') { advance(); addToken('RPAREN', null, start); continue; }
    if (ch === '[') { advance(); addToken('LBRACKET', null, start); continue; }
    if (ch === ']') { advance(); addToken('RBRACKET', null, start); continue; }
    if (ch === ';') { advance(); addToken('SEMI', null, start); continue; }
    if (ch === ',') { advance(); addToken('COMMA', null, start); continue; }
    if (ch === '=') { advance(); addToken('EQ', null, start); continue; }
    if (ch === ':') { advance(); addToken('COLON', null, start); continue; }

    if (ch === '"' || ch === "'") {
      const quote = ch;
      advance();
      let buf = '';
      while (i < src.length) {
        const curr = src[i];
        if (curr === quote) {
          advance();
          addToken('STRING', buf, start);
          buf = null;
          break;
        }
        if (curr === '\\') {
          advance();
          if (i >= src.length) {
            error('Unterminated escape sequence', start);
          }
          buf += advance();
          continue;
        }
        buf += advance();
      }
      if (buf !== null) {
        error('Unterminated string literal', start);
      }
      continue;
    }

    if ((ch === '-' && isDigit(src[i + 1])) || isDigit(ch)) {
      let j = i;
      if (src[j] === '-') j++;
      while (isDigit(src[j])) j++;
      if (src[j] === '.') {
        j++;
        if (!isDigit(src[j])) {
          error('Invalid float literal', start);
        }
        while (isDigit(src[j])) j++;
      }
      const raw = src.slice(i, j);
      advanceN(j - i);
      addToken('NUMBER', Number(raw), start);
      continue;
    }

    if (isIdentChar(ch)) {
      let j = i;
      while (j < src.length && isIdentChar(src[j])) j++;
      const ident = src.slice(i, j);
      advanceN(j - i);
      addToken('IDENT', ident, start);
      continue;
    }

    error(`Unexpected character '${ch}'`, start);
  }

  const eofPos = currentPos();
  tokens.push({ t: 'EOF', v: null, start: eofPos, end: eofPos });
  return tokens;
}

class TokenStream {
  constructor(tokens, src) {
    this.tokens = tokens;
    this.src = src;
    this.i = 0;
  }

  peek() {
    return this.tokens[this.i];
  }

  maybe(kind) {
    const tok = this.peek();
    if (tok && tok.t === kind) {
      this.i += 1;
      return tok;
    }
    return null;
  }

  take(kind, message) {
    const tok = this.peek();
    if (!tok || tok.t !== kind) {
      const friendly = friendlyName(kind);
      const got = tok ? tokenDisplay(tok) : 'end of file';
      this.error(message || `Expected ${friendly}, got ${got}`, tok);
    }
    this.i += 1;
    return tok;
  }

  error(message, tok = this.peek()) {
    const target = tok || this.tokens[this.tokens.length - 1];
    throw syntaxError(this.src, message, target.start, target.end);
  }
}

function parseSeq(stream) {
  const parts = [parseStep(stream)];
  while (stream.maybe('PIPE')) {
    parts.push(parseStep(stream));
  }
  return parts.length === 1 ? parts[0] : { node: 'Seq', children: parts };
}

function parseBlock(stream, node) {
  const children = [];
  while (true) {
    children.push(parseStep(stream));
    if (stream.maybe('SEMI')) continue;
    stream.take('RBRACE', 'Expected "}" to close block');
    break;
  }
  node.children = children;
  return node;
}

function parseRegion(stream, kind) {
  const attrs = {};
  if (stream.maybe('LPAREN')) {
    if (!stream.maybe('RPAREN')) {
      while (true) {
        const keyTok = stream.take('IDENT', 'Expected attribute name');
        stream.take('EQ', 'Expected "=" after attribute name');
        const val = parseValue(stream);
        attrs[keyTok.v] = val;
        if (stream.maybe('COMMA')) continue;
        stream.take('RPAREN', 'Expected ")" after attribute list');
        break;
      }
    }
  }
  stream.take('LBRACE', 'Expected "{" to open region body');
  return parseBlock(stream, { node: 'Region', kind, attrs, children: [] });
}

function parseStep(stream) {
  if (stream.maybe('PAR_OPEN')) return parseBlock(stream, { node: 'Par', children: [] });
  if (stream.maybe('SEQ_OPEN')) return parseBlock(stream, { node: 'Seq', children: [] });
  if (stream.maybe('REGION_AUTH')) return parseRegion(stream, 'Authorize');
  if (stream.maybe('REGION_TXN')) return parseRegion(stream, 'Transaction');
  const idTok = stream.take('IDENT', 'Expected primitive name');
  const prim = idTok.v;
  const args = {};
  if (stream.maybe('LPAREN')) {
    if (!stream.maybe('RPAREN')) {
      while (true) {
        const keyTok = stream.take('IDENT', 'Expected argument name');
        stream.take('EQ', 'Expected "=" after argument name');
        const value = parseValue(stream);
        args[keyTok.v] = value;
        if (stream.maybe('COMMA')) continue;
        stream.take('RPAREN', 'Expected ")" after argument list');
        break;
      }
    }
  }
  return { node: 'Prim', prim: prim.toLowerCase(), args };
}

function parseValue(stream) {
  const tok = stream.peek();
  switch (tok.t) {
    case 'STRING':
      stream.take('STRING');
      return tok.v;
    case 'NUMBER':
      stream.take('NUMBER');
      return tok.v;
    case 'IDENT':
      stream.take('IDENT');
      if (tok.v === 'true') return true;
      if (tok.v === 'false') return false;
      if (tok.v === 'null') return null;
      return tok.v;
    case 'LBRACKET':
      return parseArray(stream);
    case 'LBRACE':
      return parseObject(stream);
    default:
      stream.error('Expected value', tok);
  }
}

function parseArray(stream) {
  stream.take('LBRACKET');
  const items = [];
  if (stream.maybe('RBRACKET')) return items;
  while (true) {
    items.push(parseValue(stream));
    if (stream.maybe('COMMA')) {
      if (stream.maybe('RBRACKET')) break;
      continue;
    }
    stream.take('RBRACKET', 'Expected "]" to close array');
    break;
  }
  return items;
}

function parseObject(stream) {
  stream.take('LBRACE');
  const obj = {};
  if (stream.maybe('RBRACE')) return obj;
  while (true) {
    const keyTok = stream.peek();
    let key;
    if (keyTok.t === 'STRING') {
      stream.take('STRING');
      key = keyTok.v;
    } else if (keyTok.t === 'IDENT') {
      stream.take('IDENT');
      key = keyTok.v;
    } else {
      stream.error('Expected string or identifier for object key', keyTok);
    }
    stream.take('COLON', 'Expected ":" after object key');
    const value = parseValue(stream);
    obj[key] = value;
    if (stream.maybe('COMMA')) {
      if (stream.maybe('RBRACE')) break;
      continue;
    }
    stream.take('RBRACE', 'Expected "}" to close object');
    break;
  }
  return obj;
}

function friendlyName(kind) {
  switch (kind) {
    case 'IDENT': return 'identifier';
    case 'STRING': return 'string';
    case 'NUMBER': return 'number';
    case 'LPAREN': return "'('";
    case 'RPAREN': return "')'";
    case 'EQ': return "'='";
    case 'COMMA': return "','";
    case 'RBRACE': return "'}'";
    case 'LBRACE': return "'{'";
    case 'RBRACKET': return "']'";
    case 'LBRACKET': return "'['";
    case 'COLON': return "':'";
    default: return kind.toLowerCase();
  }
}

function tokenDisplay(tok) {
  if (!tok) return 'end of file';
  if (tok.t === 'EOF') return 'end of file';
  if (tok.t === 'IDENT') return `'${tok.v}'`;
  return tok.t.toLowerCase();
}

function syntaxError(src, message, start, end) {
  const lines = src.split(/\r?\n/);
  const lineIndex = Math.max(0, (start ? start.line : 1) - 1);
  const lineText = lines[lineIndex] ?? '';
  const col = start ? start.col : 1;
  const caretStart = Math.max(0, col - 1);
  const spanLength = Math.min(Math.max((end.index - start.index) || 1, 2), 12);
  const available = Math.max(lineText.length - caretStart, 1);
  const caretLen = Math.min(spanLength, available < 2 ? 2 : available);
  const caret = ' '.repeat(caretStart) + '^'.repeat(caretLen);
  const err = new Error(`${start.line}:${col} ${message}\n${lineText}\n${caret}`);
  err.name = 'SyntaxError';
  return err;
}
