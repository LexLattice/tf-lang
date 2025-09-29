#!/usr/bin/env node
// Minimal LSP stdio client for probes (init, diagnostics, hover, codeAction)
import { spawn } from 'node:child_process';
import { readFile } from 'node:fs/promises';

function hdr(len) { return `Content-Length: ${len}\r\n\r\n`; }
function send(child, obj) {
  const s = JSON.stringify({ jsonrpc: "2.0", ...obj });
  child.stdin.write(hdr(Buffer.byteLength(s)) + s);
}
function nextId() { return ++nextId._; } nextId._ = 0;

function parseStream(onMsg) {
  let buf = Buffer.alloc(0);
  return chunk => {
    buf = Buffer.concat([buf, chunk]);
    while (true) {
      const hdrEnd = buf.indexOf('\r\n\r\n');
      if (hdrEnd < 0) break;
      const headers = buf.slice(0, hdrEnd).toString('utf8');
      const m = /Content-Length:\s*(\d+)/i.exec(headers);
      if (!m) { buf = buf.slice(hdrEnd + 4); continue; }
      const len = parseInt(m[1], 10);
      const start = hdrEnd + 4;
      if (buf.length < start + len) break;
      const body = buf.slice(start, start + len).toString('utf8');
      buf = buf.slice(start + len);
      try { onMsg(JSON.parse(body)); } catch { }
    }
  };
}

async function main() {
  const args = process.argv.slice(2);
  const mode = args.includes('--mode') ? args[args.indexOf('--mode') + 1] : 'init';
  const file = args.includes('--file') ? args[args.indexOf('--file') + 1] : null;
  const symbol = args.includes('--symbol') ? args[args.indexOf('--symbol') + 1] : null;
  const rangeArg = args.includes('--range') ? args[args.indexOf('--range') + 1] : null;
  const posArg = args.includes('--position') ? args[args.indexOf('--position') + 1] : null;
  const grep = args.includes('--grep') ? args[args.indexOf('--grep') + 1] : null;
  const select = args.includes('--select') ? args[args.indexOf('--select') + 1] : null;
  const expect = args.includes('--expect') ? args[args.indexOf('--expect') + 1] : null;

  const srv = spawn(process.execPath, ['packages/tf-lsp-server/bin/server.mjs', '--stdio'], { stdio: ['pipe', 'pipe', 'inherit'] });
  const onChunk = parseStream(onMsg);
  srv.stdout.on('data', onChunk);

  const pending = new Map();
  function req(method, params) {
    const id = nextId(); pending.set(id, { method });
    send(srv, { id, method, params });
    return new Promise((res, rej) => {
      pending.get(id).res = res; pending.get(id).rej = rej;
      setTimeout(() => rej(new Error('timeout ' + method)), 3000);
    });
  }
  function notif(method, params) { send(srv, { method, params }); }

  const diags = [];
  function onMsg(msg) {
    if (msg.id !== undefined && pending.has(msg.id)) {
      const { res } = pending.get(msg.id); pending.delete(msg.id); res(msg);
    } else if (msg.method === 'textDocument/publishDiagnostics') {
      diags.push(msg.params);
    }
  }

  const init = await req('initialize', { processId: null, rootUri: null, capabilities: {} });
  if (mode === 'init') {
    console.log(JSON.stringify({ capabilities: init.result?.capabilities || {} }, null, 2));
    srv.stdin.end(); return;
  }

  if (!file) throw new Error('--file required for diagnostics/hover/codeAction');
  const uri = 'file:///' + file;
  const text = await readFile(file, 'utf8');
  notif('initialized', {});
  notif('textDocument/didOpen', { textDocument: { uri, languageId: 'tf', version: 1, text } });

  if (mode === 'diagnostics') {
    // Wait a bit for publishDiagnostics, print first payload
    await new Promise(r => setTimeout(r, 400));
    const first = diags[0] || { uri, diagnostics: [] };
    console.log(JSON.stringify(first, null, 2));
    process.exit(0);
  }

  if (mode === 'hover') {
    // naive position: start of file or first match of symbol
    let pos = { line: 0, character: 0 };
    if (posArg) {
      pos = parsePosition(posArg);
    } else if (symbol) {
      const idx = text.indexOf(symbol.split('/').pop().split('@')[0]);
      if (idx >= 0) {
        const pre = text.slice(0, idx);
        const line = (pre.match(/\n/g) || []).length;
        const col = idx - (pre.lastIndexOf('\n') + 1);
        pos = { line, character: col + 1 };
      }
    }
    const hv = await req('textDocument/hover', { textDocument: { uri }, position: pos });
    if (expect) {
      const payload = hv.result || null;
      const markdown = typeof payload?.contents === 'string'
        ? payload.contents
        : payload?.contents?.value || '';
      const matches = typeof markdown === 'string' && markdown.includes(`**${expect}**`);
      if (!matches) {
        console.error(JSON.stringify({
          expect,
          position: pos,
          received: payload
        }, null, 2));
        process.exit(2);
      }
    }
    console.log(JSON.stringify(hv.result || {}, null, 2));
    process.exit(0);
  }

  if (mode === 'codeAction') {
    const defaultPos = { line: 0, character: 0 };
    const selectionRange = select ? findSelectionRange(text, select) : null;
    let parsedRange = selectionRange || parseRange(rangeArg, posArg);
    if (!parsedRange) {
      parsedRange = findDuplicateWordRange(text) || { start: defaultPos, end: defaultPos };
    }
    const ca = await req('textDocument/codeAction', {
      textDocument: { uri },
      range: parsedRange,
      context: { diagnostics: diags[0]?.diagnostics || [] }
    });
    const items = ca.result || [];
    const titles = items.map(x => x.title || '');
    console.log(JSON.stringify({ titles }, null, 2));
    const ok = grep
      ? titles.some(t => t.includes(grep))
      : titles.some(t => /Authorize/.test(t));
    process.exit(ok ? 0 : 2);
  }
}

function parseRange(rangeArg, posArg) {
  if (rangeArg) {
    const [startStr, endStr] = rangeArg.split('-');
    const start = parsePosition(startStr);
    const end = parsePosition(endStr || startStr);
    return { start, end };
  }
  if (posArg) {
    const pos = parsePosition(posArg);
    return { start: pos, end: pos };
  }
  return null;
}

function parsePosition(text) {
  if (!text) return { line: 0, character: 0 };
  const [lineStr, charStr] = text.split(':');
  const line = Number(lineStr) || 0;
  const character = Number(charStr) || 0;
  return { line, character };
}

function findSelectionRange(content, snippet) {
  if (!snippet) return null;
  const idx = content.indexOf(snippet);
  if (idx < 0) return null;
  const start = offsetToPosition(content, idx);
  const end = offsetToPosition(content, idx + snippet.length);
  return { start, end };
}

function offsetToPosition(text, offset) {
  const clamped = Math.max(0, Math.min(offset, text.length));
  let line = 0;
  let character = 0;
  for (let i = 0; i < clamped; i++) {
    if (text[i] === '\n') {
      line++;
      character = 0;
    } else {
      character++;
    }
  }
  return { line, character };
}

function findDuplicateWordRange(text) {
  const regex = /\b[A-Za-z_][A-Za-z0-9_]*\b/g;
  const seen = new Map();
  let match;
  while ((match = regex.exec(text)) !== null) {
    const word = match[0];
    const record = seen.get(word);
    if (!record) {
      seen.set(word, { count: 1, index: match.index });
    } else {
      record.count += 1;
      if (record.count === 2 && record.index != null) {
        const start = offsetToPosition(text, record.index);
        const end = offsetToPosition(text, record.index + word.length);
        return { start, end };
      }
    }
  }
  return null;
}
main().catch(e => { console.error(e.stack || String(e)); process.exit(2); });
