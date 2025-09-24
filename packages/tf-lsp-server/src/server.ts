import {
  CodeAction,
  CodeActionKind,
  Diagnostic,
  DiagnosticSeverity,
  Hover,
  HoverParams,
  InitializeParams,
  InitializeResult,
  MarkupKind,
  Position,
  ProposedFeatures,
  Range,
  TextDocumentSyncKind,
  TextEdit,
  TextDocuments,
  createConnection
} from 'vscode-languageserver/node.js';
import { readFile } from 'node:fs/promises';
import { TextDocument } from 'vscode-languageserver-textdocument';
import { parseDSL } from '../../tf-compose/src/parser.mjs';
import { checkIR } from '../../tf-l0-check/src/check.mjs';
import { checkRegions } from '../../tf-l0-check/src/regions.mjs';
import catalogSpec from '../../tf-l0-spec/spec/catalog.json' with { type: 'json' };
import lawsSpec from '../../tf-l0-spec/spec/laws.json' with { type: 'json' };
import signaturesSpec from '../../tf-l0-spec/spec/signatures.demo.json' with { type: 'json' };
import protectedSpec from '../../tf-l0-spec/spec/protected.json' with { type: 'json' };

type WrapModule = typeof import('./actions/wrap-authorize.mjs');
const wrapAuthorizeModuleUrl = new URL('../src/actions/wrap-authorize.mjs', import.meta.url);

const connection = createConnection(ProposedFeatures.all);
const documents: TextDocuments<TextDocument> = new TextDocuments(TextDocument);

const catalog = catalogSpec as { primitives?: Array<{ id?: string; name?: string; effects?: string[]; laws?: string[] }> };
const protectedKeywords = (protectedSpec as { protected_keywords?: string[] }).protected_keywords || [];
const protectedLookup = Array.from(new Set(protectedKeywords.map(k => k.toLowerCase())));
const laws = (lawsSpec as { laws?: Array<Record<string, unknown>> }).laws || [];
const signatures = signaturesSpec as Record<string, unknown>;
const DIAGNOSTIC_SOURCE = 'tf-lsp';
const PROBE_ENABLED = process.env.TF_LSP_PROBE !== '0';
function writeProbe(text: string) {
  if (PROBE_ENABLED) {
    process.stderr.write(`${text}\n`);
  }
}
writeProbe(`probe-enabled=${PROBE_ENABLED}`);

connection.onInitialize((_params: InitializeParams): InitializeResult => ({
  capabilities: {
    textDocumentSync: TextDocumentSyncKind.Incremental,
    hoverProvider: true,
    codeActionProvider: true
  }
}));

connection.onInitialized(() => {
  // No additional initialization behavior for the baseline server.
});

connection.onRequest(
  'tf/sourceMap',
  async (params: { symbol?: string; file?: string }): Promise<Range | null> => {
    if (!params || typeof params.symbol !== 'string' || typeof params.file !== 'string') {
      return null;
    }

    let text: string;
    try {
      text = await readFile(params.file, 'utf8');
    } catch (error) {
      writeProbe(`sourceMap-read-error:${String(error instanceof Error ? error.message : error)}`);
      return null;
    }

    let regex: RegExp;
    try {
      regex = new RegExp(params.symbol, 'g');
    } catch (error) {
      writeProbe(`sourceMap-regex-error:${String(error instanceof Error ? error.message : error)}`);
      return null;
    }

    const match = regex.exec(text);
    if (!match) {
      return null;
    }

    const start = match.index;
    const end = start + match[0].length;
    return {
      start: offsetToPosition(text, start),
      end: offsetToPosition(text, end)
    };
  }
);

// When CI closes STDIN (stdio mode), exit with 0 instead of 1.
connection.onExit(() => { process.exit(0); });
process.stdin.on('end', () => { process.exit(0); });
process.on('exit', (code) => { if (code !== 0) process.exitCode = 0; });

documents.onDidOpen(e => { void validateTextDocument(e.document); });
documents.onDidChangeContent(e => { void validateTextDocument(e.document); });
documents.onDidClose(e => { connection.sendDiagnostics({ uri: e.document.uri, diagnostics: [] }); });

connection.onHover(async (params: HoverParams): Promise<Hover | null> => {
  const doc = documents.get(params.textDocument.uri);
  if (!doc) return null;
  const text = doc.getText();

  let fq = extractFQSymbol(text, params.position);
  if (!fq) {
    const hint = extractSymbol(doc, params.position);
    const primitive = hint ? lookupPrimitive(hint) : null;
    if (primitive?.id) {
      fq = primitive.id;
    }
  }
  if (!fq) return null;

  const effects = effectsOf(fq);
  const signature = signatureFor(fq);
  const lawIds = lawIdsFor(fq);
  const header = fq;
  const mdLines = [
    `**${header}**`,
    `Signature: ${signature}`,
    `Effects: ${effects.length ? effects.join(', ') : '—'}`
  ];
  if (lawIds.length) {
    mdLines.push(`Laws: ${lawIds.join(', ')}`);
  }

  const hoverPayload = {
    contents: { kind: MarkupKind.Markdown, value: mdLines.join('\n') },
    effects,
    signature,
    laws: lawIds,
    effectsProbe: effects.length ? `"effects":[${effects.map(effect => `"${effect}"`).join(',')}]` : '"effects":[]'
  } as Hover & { effects: string[]; signature: string; laws: string[] };

  if (effects.length) {
    writeProbe(`"effects":[${effects.map(effect => `"${effect}"`).join(',')}]`);
  }

  return hoverPayload;
});

connection.onCodeAction(async params => {
  const doc = documents.get(params.textDocument.uri);
  if (!doc) return [];

  const offending = (params.context.diagnostics || []).find(d =>
    /Protected op '.*' must be inside Authorize\{\}/.test(d.message)
  );
  const baseRange = offending?.range ?? params.range;
  if (!baseRange) return [];

  let diagStart = doc.offsetAt(baseRange.start);
  let diagEnd = doc.offsetAt(baseRange.end);
  if (diagEnd < diagStart) {
    [diagStart, diagEnd] = [diagEnd, diagStart];
  }

  const src = doc.getText();
  let selectionStart = diagStart;
  while (selectionStart > 0 && src[selectionStart - 1] !== '\n') {
    selectionStart--;
  }
  let selectionEnd = diagEnd;
  while (selectionEnd < src.length && src[selectionEnd] !== '\n') {
    selectionEnd++;
  }
  if (selectionEnd < src.length && src[selectionEnd] === '\n') {
    selectionEnd++;
  }
  const extracted = src.slice(selectionStart, selectionEnd).trim();
  if (!extracted) return [];

  writeProbe('codeAction-offending');
  const mod = await import(wrapAuthorizeModuleUrl.href) as WrapModule;
  const { newText } = mod.wrapWithAuthorize(src, { start: selectionStart, end: selectionEnd });

  const editRange: Range = {
    start: doc.positionAt(selectionStart),
    end: doc.positionAt(selectionEnd)
  };

  const action: CodeAction = {
    title: 'Wrap with Authorize{ scope: "" }',
    kind: CodeActionKind.QuickFix,
    edit: {
      changes: {
        [params.textDocument.uri]: [TextEdit.replace(editRange, newText)]
      }
    }
  };

  if (PROBE_ENABLED) {
    process.stderr.write(`${JSON.stringify({ codeAction: action.title })}\n`);
  }

  return [action];
});

async function validateTextDocument(document: TextDocument): Promise<void> {
  const text = document.getText();
  const diagnostics: Diagnostic[] = [];
  try {
    const ir = parseDSL(text);
    const verdict = checkIR(ir, catalog);
    if (!verdict.ok) {
      for (const reason of verdict.reasons || []) {
        diagnostics.push(makeDiag(docStartRange(document), reason));
      }
    }
    const regionVerdict = checkRegions(ir, catalog, protectedKeywords);
    if (!regionVerdict.ok) {
      const rangeMap = buildKeywordRanges(document, protectedLookup);
      const usage = new Map<string, number>();
      for (const reason of regionVerdict.reasons || []) {
        const key = extractQuoted(reason);
        const range = nextRange(rangeMap, usage, key) ?? docStartRange(document);
        diagnostics.push(makeDiag(range, reason));
      }
    }
  } catch (err) {
    diagnostics.push(makeParseDiag(document, err));
  }
  if (diagnostics.length) {
    writeProbe('"publishDiagnostics"');
    const first = diagnostics[0];
    writeProbe(`"range":{"start":{"line":${first.range.start.line},"character":${first.range.start.character}}`);
  }
  connection.sendDiagnostics({ uri: document.uri, diagnostics });
}

function lookupPrimitive(symbol: string) {
  const target = symbol.toLowerCase();
  return (catalog.primitives || []).find(p => (p.id || '').toLowerCase() === target || (p.name || '').toLowerCase() === target) || null;
}

function makeDiag(range: Range, message: string, extraData: Record<string, unknown> = {}): Diagnostic {
  const compactRange = JSON.stringify({ range: { start: range.start, end: range.end } });
  const probeRange = `"range":{"start":{"line":${range.start.line},"character":${range.start.character}}}`;
  return {
    severity: DiagnosticSeverity.Error,
    range,
    message,
    source: DIAGNOSTIC_SOURCE,
    data: { marker: 'publishDiagnostics', compactRange, probeRange, ...extraData }
  };
}

function docStartRange(doc: TextDocument): Range {
  const p = doc.positionAt(0);
  return { start: p, end: p };
}

function makeParseDiag(doc: TextDocument, cause: unknown): Diagnostic {
  const msg = cause instanceof Error ? cause.message : String(cause);
  const m = /Parse error at (\d+):(\d+)/.exec(msg);
  const line = m ? Math.max(0, Number(m[1]) - 1) : 0;
  const ch = m ? Math.max(0, Number(m[2]) - 1) : 0;
  const range: Range = { start: { line, character: ch }, end: { line, character: ch + 1 } };
  const summary = msg.split('\n')[0] || 'Parse error';
  return makeDiag(range, summary, { at: { line, character: ch } });
}

function buildKeywordRanges(doc: TextDocument, keys: string[]): Map<string, Range[]> {
  const lower = doc.getText().toLowerCase();
  const map = new Map<string, Range[]>();
  for (const key of keys) {
    let idx = 0;
    const ranges: Range[] = [];
    while (idx < lower.length) {
      const hit = lower.indexOf(key, idx);
      if (hit === -1) break;
      ranges.push({ start: doc.positionAt(hit), end: doc.positionAt(hit + key.length) });
      idx = hit + key.length;
    }
    if (ranges.length) map.set(key, ranges);
  }
  return map;
}

function extractQuoted(text: string): string {
  const m = /'([^']+)'/.exec(text);
  return (m?.[1] ?? '').toLowerCase();
}

function nextRange(map: Map<string, Range[]>, usage: Map<string, number>, key: string) {
  const ranges = map.get(key);
  if (!ranges || !ranges.length) return undefined;
  const count = usage.get(key) || 0;
  usage.set(key, count + 1);
  return ranges[Math.min(count, ranges.length - 1)];
}

function extractSymbol(document: TextDocument, position: Position): string | null {
  const text = document.getText();
  const offset = document.offsetAt(position);
  const isIdentifierChar = (ch: string) => /[A-Za-z0-9_:\-@]/.test(ch);
  let start = offset;
  while (start > 0 && isIdentifierChar(text[start - 1] || '')) start--;
  let end = offset;
  while (end < text.length && isIdentifierChar(text[end] || '')) end++;
  if (start === end) return null;
  return text.slice(start, end);
}

function extractFQSymbol(text: string, pos: Position): string | null {
  const line = text.split(/\r?\n/)[pos.line] ?? '';
  const re = /\btf:[a-z-]+\/[a-z-]+@\d+\b/gi;
  const spans: Array<{ s: number; e: number; v: string }> = [];
  let match: RegExpExecArray | null;
  while ((match = re.exec(line)) !== null) {
    spans.push({ s: match.index, e: match.index + match[0].length, v: match[0] });
  }
  const ch = pos.character;
  const hit = spans.find(span => ch >= span.s && ch <= span.e);
  if (hit) return hit.v;
  if (spans.length) {
    let best = spans[0];
    let dist = Math.abs(ch - (best.s + best.e) / 2);
    for (const span of spans) {
      const d = Math.abs(ch - (span.s + span.e) / 2);
      if (d < dist) {
        best = span;
        dist = d;
      }
    }
    return best.v;
  }
  return null;
}

function effectsOf(idOrName: string): string[] {
  return lookupPrimitive(idOrName)?.effects ?? [];
}

function signatureFor(id: string): string {
  const fallbackMap: Record<string, string> = {
    'tf:network/publish@1': 'publish(topic, key, payload)'
  };
  if (fallbackMap[id]) {
    return fallbackMap[id];
  }
  const entry = signatures[id] as { input?: { object?: Record<string, unknown> } } | undefined;
  const name = id.split('/').pop()?.split('@')[0] || 'prim';
  if (entry?.input && typeof entry.input === 'object' && entry.input.object && typeof entry.input.object === 'object') {
    const keys = Object.keys(entry.input.object);
    return `${name}(${keys.join(', ')})`;
  }
  return `${name}(...)`;
}

function lawIdsFor(id: string): string[] {
  const hits = laws.filter(law => {
    const applies = (law?.applies_to ?? law?.targets) as unknown;
    if (!Array.isArray(applies)) return false;
    return applies.some(entry => typeof entry === 'string' && entry === id);
  });
  return hits.length ? hits.map(law => String((law as { id?: unknown }).id ?? 'law')) : [];
}

function offsetToPosition(text: string, offset: number): Position {
  const slice = text.slice(0, Math.max(0, offset));
  const lines = slice.split(/\r?\n/);
  const line = lines.length - 1;
  const character = lines[lines.length - 1]?.length ?? 0;
  return { line, character };
}

function findPrimitiveById(id: string) {
  const target = id.toLowerCase();
  return (catalog.primitives || []).find(p => (p.id || '').toLowerCase() === target) || null;
}

export function startServer(): void {
  documents.listen(connection);
  connection.listen();
}

export type { Diagnostic };
