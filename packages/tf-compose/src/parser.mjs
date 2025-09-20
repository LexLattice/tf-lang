// DSL parser (extended) supporting regions: authorize{ ... } and txn{ ... }
export function parseDSL(src) {
  const tokens = tokenize(src);
  const parser = new Parser(src, tokens);
  const seq = parseSeq(parser);
  parser.expectEOF();
  return seq;
}

function tokenize(s) {
  const tokens = [];
  let i = 0;
  let line = 1;
  let col = 1;

  const push = (t, v, start, end, lineStart, colStart) => {
    tokens.push({ t, v, start, end, line: lineStart, col: colStart });
  };

  const advanceChar = () => {
    const ch = s[i];
    i++;
    if (ch === '\n') { line++; col = 1; }
    else { col++; }
    return ch;
  };

  while (i < s.length) {
    const start = i;
    const lineStart = line;
    const colStart = col;
    const c = s[i];

    if (/\s/.test(c)) { advanceChar(); continue; }

    if (s.startsWith('|>', i)) {
      advanceChar(); advanceChar();
      push('PIPE', '|>', start, i, lineStart, colStart);
      continue;
    }

    if (s.startsWith('par{', i)) {
      advanceChar(); advanceChar(); advanceChar(); advanceChar();
      push('PAR_OPEN', 'par{', start, i, lineStart, colStart);
      continue;
    }

    if (s.startsWith('seq{', i)) {
      advanceChar(); advanceChar(); advanceChar(); advanceChar();
      push('SEQ_OPEN', 'seq{', start, i, lineStart, colStart);
      continue;
    }

    if (s.startsWith('authorize', i) && (s[i + 9] === '{' || s[i + 9] === '(')) {
      for (let k = 0; k < 9; k++) advanceChar();
      push('REGION_AUTH', 'authorize', start, i, lineStart, colStart);
      continue;
    }

    if (s.startsWith('txn', i) && (s[i + 3] === '{' || s[i + 3] === '(')) {
      for (let k = 0; k < 3; k++) advanceChar();
      push('REGION_TXN', 'txn', start, i, lineStart, colStart);
      continue;
    }

    if (c === '{') { advanceChar(); push('LBRACE', '{', start, i, lineStart, colStart); continue; }
    if (c === '}') { advanceChar(); push('RBRACE', '}', start, i, lineStart, colStart); continue; }
    if (c === '(') { advanceChar(); push('LPAREN', '(', start, i, lineStart, colStart); continue; }
    if (c === ')') { advanceChar(); push('RPAREN', ')', start, i, lineStart, colStart); continue; }
    if (c === '[') { advanceChar(); push('LBRACKET', '[', start, i, lineStart, colStart); continue; }
    if (c === ']') { advanceChar(); push('RBRACKET', ']', start, i, lineStart, colStart); continue; }
    if (c === ';') { advanceChar(); push('SEMI', ';', start, i, lineStart, colStart); continue; }
    if (c === ',') { advanceChar(); push('COMMA', ',', start, i, lineStart, colStart); continue; }
    if (c === '=') { advanceChar(); push('EQ', '=', start, i, lineStart, colStart); continue; }
    if (c === ':') { advanceChar(); push('COLON', ':', start, i, lineStart, colStart); continue; }

    if (c === '"' || c === '\'') {
      const quote = c;
      advanceChar();
      let buf = '';
      let closed = false;
      while (i < s.length) {
        const ch = s[i];
        if (ch === quote) { advanceChar(); closed = true; break; }
        if (ch === '\\') {
          advanceChar();
          if (i >= s.length) throw formatError(s, start, i, 'Unterminated string');
          buf += advanceChar();
          continue;
        }
        buf += ch;
        advanceChar();
      }
      if (!closed) throw formatError(s, start, i, 'Unterminated string');
      push('STRING', buf, start, i, lineStart, colStart);
      continue;
    }

    if (/[0-9]/.test(c) || (c === '-' && /[0-9]/.test(s[i + 1] || ''))) {
      let hasDigits = false;
      let text = '';
      if (s[i] === '-') { text += advanceChar(); }
      while (i < s.length && /[0-9]/.test(s[i])) { hasDigits = true; text += advanceChar(); }
      let fracDigits = 0;
      if (s[i] === '.') {
        text += advanceChar();
        while (i < s.length && /[0-9]/.test(s[i])) { fracDigits++; text += advanceChar(); }
      }
      if (!hasDigits && fracDigits === 0) throw formatError(s, start, i, 'Invalid number');
      push('NUMBER', Number(text), start, i, lineStart, colStart);
      continue;
    }

    if (/[A-Za-z_]/.test(c)) {
      let text = '';
      while (i < s.length && /[A-Za-z0-9_\-\.]/.test(s[i])) text += advanceChar();
      push('IDENT', text, start, i, lineStart, colStart);
      continue;
    }

    if (c === '-' || c === '.') {
      let text = '';
      while (i < s.length && /[A-Za-z0-9_\-\.]/.test(s[i])) text += advanceChar();
      push('IDENT', text, start, i, lineStart, colStart);
      continue;
    }

    throw formatError(s, start, start + 1, `Unexpected character '${c}'`);
  }

  tokens.push({ t: 'EOF', v: null, start: s.length, end: s.length, line, col });
  return tokens;
}

class Parser {
  constructor(src, tokens) {
    this.src = src;
    this.tokens = tokens;
    this.i = 0;
  }
  peek() { return this.tokens[this.i] || this.tokens[this.tokens.length - 1]; }
  take(kind) {
    const tok = this.peek();
    if (tok.t !== kind) this.fail(tok, `Expected ${kind}, got ${tok.t}`);
    this.i++;
    return tok;
  }
  maybe(kind) {
    const tok = this.peek();
    if (tok.t === kind) { this.i++; return tok; }
    return null;
  }
  expectEOF() {
    const tok = this.peek();
    if (tok.t !== 'EOF') this.fail(tok, 'Trailing tokens');
  }
  fail(tok, message) {
    throw formatError(this.src, tok.start, Math.max(tok.end, tok.start + 1), message);
  }
  errorAt(tok, message) {
    throw formatError(this.src, tok.start, Math.max(tok.end, tok.start + 1), message);
  }
}

function parseSeq(parser) {
  const parts = [parseStep(parser)];
  while (parser.maybe('PIPE')) parts.push(parseStep(parser));
  return parts.length === 1 ? parts[0] : { node: 'Seq', children: parts };
}

function parseBlock(parser, node) {
  const kids = [];
  if (parser.maybe('RBRACE')) { node.children = kids; return node; }
  while (true) {
    kids.push(parseStep(parser));
    if (parser.maybe('SEMI')) {
      if (parser.maybe('RBRACE')) break;
      continue;
    }
    parser.take('RBRACE');
    break;
  }
  node.children = kids;
  return node;
}

function parseRegion(parser, kind) {
  let attrs = {};
  if (parser.maybe('LPAREN')) {
    if (!parser.maybe('RPAREN')) {
      attrs = parseAssignments(parser, 'RPAREN');
    }
  }
  parser.take('LBRACE');
  return parseBlock(parser, { node: 'Region', kind, attrs, children: [] });
}

function parseAssignments(parser, closing) {
  const out = {};
  while (true) {
    const keyTok = parser.take('IDENT');
    parser.take('EQ');
    out[keyTok.v] = parseValue(parser);
    if (parser.maybe('COMMA')) {
      if (parser.maybe(closing)) break;
      continue;
    }
    parser.take(closing);
    break;
  }
  return out;
}

function parseStep(parser) {
  if (parser.maybe('PAR_OPEN')) return parseBlock(parser, { node: 'Par', children: [] });
  if (parser.maybe('SEQ_OPEN')) return parseBlock(parser, { node: 'Seq', children: [] });
  if (parser.maybe('REGION_AUTH')) return parseRegion(parser, 'Authorize');
  if (parser.maybe('REGION_TXN')) return parseRegion(parser, 'Transaction');
  const id = parser.take('IDENT').v;
  const args = {};
  if (parser.maybe('LPAREN')) {
    if (!parser.maybe('RPAREN')) {
      Object.assign(args, parseAssignments(parser, 'RPAREN'));
    }
  }
  return { node: 'Prim', prim: id.toLowerCase(), args };
}

function parseValue(parser) {
  const tok = parser.peek();
  switch (tok.t) {
    case 'STRING': parser.take('STRING'); return tok.v;
    case 'NUMBER': parser.take('NUMBER'); return tok.v;
    case 'IDENT': {
      parser.take('IDENT');
      if (tok.v === 'true') return true;
      if (tok.v === 'false') return false;
      if (tok.v === 'null') return null;
      return tok.v;
    }
    case 'LBRACE':
      return parseObject(parser);
    case 'LBRACKET':
      return parseArray(parser);
    default:
      parser.errorAt(tok, 'Expected value');
  }
}

function parseObject(parser) {
  parser.take('LBRACE');
  const obj = {};
  if (parser.maybe('RBRACE')) return obj;
  while (true) {
    const keyTok = parser.peek();
    let key;
    if (keyTok.t === 'STRING') { parser.take('STRING'); key = keyTok.v; }
    else if (keyTok.t === 'IDENT') { parser.take('IDENT'); key = keyTok.v; }
    else parser.errorAt(keyTok, 'Expected object key');
    parser.take('COLON');
    obj[key] = parseValue(parser);
    if (parser.maybe('COMMA')) {
      if (parser.maybe('RBRACE')) break;
      continue;
    }
    parser.take('RBRACE');
    break;
  }
  return obj;
}

function parseArray(parser) {
  parser.take('LBRACKET');
  const items = [];
  if (parser.maybe('RBRACKET')) return items;
  while (true) {
    items.push(parseValue(parser));
    if (parser.maybe('COMMA')) {
      if (parser.maybe('RBRACKET')) break;
      continue;
    }
    parser.take('RBRACKET');
    break;
  }
  return items;
}

function formatError(src, start, end, message) {
  const { line, column, lineText } = locate(src, start);
  const spanBase = Math.max(1, end - start);
  const span = Math.max(2, Math.min(12, spanBase));
  const caret = ' '.repeat(Math.max(0, column - 1)) + '^'.repeat(span);
  const err = new Error(`${message} at ${line}:${column}\n${lineText}\n${caret}`);
  err.line = line;
  err.column = column;
  return err;
}

function locate(src, index) {
  const len = src.length;
  const clamped = Math.max(0, Math.min(index, len));
  let line = 1;
  let lineStart = 0;
  for (let i = 0; i < clamped; i++) {
    if (src[i] === '\n') {
      line++;
      lineStart = i + 1;
    }
  }
  const column = clamped - lineStart + 1;
  const lineEndIdx = src.indexOf('\n', lineStart);
  const lineEnd = lineEndIdx === -1 ? len : lineEndIdx;
  const lineText = src.slice(lineStart, lineEnd);
  if (index > len && src.length > 0 && src[len - 1] === '\n') {
    return { line: line + 1, column: 1, lineText: '' };
  }
  return { line, column, lineText };
}
