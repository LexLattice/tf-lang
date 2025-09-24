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
    if (symbol) {
      const idx = text.indexOf(symbol.split('/').pop().split('@')[0]);
      if (idx >= 0) {
        const pre = text.slice(0, idx);
        const line = (pre.match(/\n/g) || []).length;
        const col = idx - (pre.lastIndexOf('\n') + 1);
        pos = { line, character: col + 1 };
      }
    }
    const hv = await req('textDocument/hover', { textDocument: { uri }, position: pos });
    console.log(JSON.stringify(hv.result || {}, null, 2));
    process.exit(0);
  }

  if (mode === 'codeAction') {
    const ca = await req('textDocument/codeAction', { textDocument: { uri }, range: { start: { line: 0, character: 0 }, end: { line: 0, character: 0 } }, context: { diagnostics: diags[0]?.diagnostics || [] } });
    const items = ca.result || [];
    const titles = items.map(x => x.title || '');
    console.log(JSON.stringify({ titles }, null, 2));
    process.exit(titles.some(t => /Authorize/.test(t)) ? 0 : 2);
  }
}
main().catch(e => { console.error(e.stack || String(e)); process.exit(2); });
