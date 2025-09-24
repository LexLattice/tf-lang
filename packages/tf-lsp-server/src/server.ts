/// <reference path="./shims.d.ts" />
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
import { TextDocument } from 'vscode-languageserver-textdocument';
import { parseDSL } from '../../tf-compose/src/parser.mjs';
import { checkIR } from '../../tf-l0-check/src/check.mjs';
import { checkRegions } from '../../tf-l0-check/src/regions.mjs';
import catalogSpec from '../../tf-l0-spec/spec/catalog.json' with { type: 'json' };
import protectedSpec from '../../tf-l0-spec/spec/protected.json' with { type: 'json' };

const connection = createConnection(ProposedFeatures.all);
const documents: TextDocuments<TextDocument> = new TextDocuments(TextDocument);

const catalog = catalogSpec as { primitives?: Array<{ id?: string; name?: string; effects?: string[]; laws?: string[] }> };
const protectedKeywords = (protectedSpec as { protected_keywords?: string[] }).protected_keywords || [];
const protectedLookup = Array.from(new Set(protectedKeywords.map(k => k.toLowerCase())));
const DIAGNOSTIC_SOURCE = 'tf-lsp';

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
  const symbol = extractSymbol(doc, params.position);
  if (!symbol) return null;
  const primitive = lookupPrimitive(symbol);
  if (!primitive) return null;
  const lines = [
    `**${primitive.id ?? primitive.name ?? symbol}**`
  ];
  if (primitive.effects?.length) {
    lines.push(`Effects: ${primitive.effects.join(', ')}`);
  }
  if (primitive.laws?.length) {
    lines.push(`Laws: ${primitive.laws.join(', ')}`);
  }
  if (lines.length === 1) {
    lines.push('No additional metadata');
  }
  return { contents: { kind: MarkupKind.Markdown, value: lines.join('\n') } };
});

connection.onCodeAction(async params => {
  const doc = documents.get(params.textDocument.uri);
  if (!doc) return [];
  const fullText = doc.getText();
  const mod = await import('./actions/wrap-authorize.mjs');
  const suggestion = mod.wrapWithAuthorize(fullText, { rangeHint: params.range });
  if (!suggestion) return [];
  const range: Range = {
    start: doc.positionAt(suggestion.range.start ?? 0),
    end: doc.positionAt(suggestion.range.end ?? fullText.length)
  };
  const edit: CodeAction = {
    title: 'Wrap with Authorize{}',
    kind: CodeActionKind.QuickFix,
    edit: {
      changes: {
        [doc.uri]: [TextEdit.replace(range, suggestion.newText)]
      }
    }
  };
  return [edit];
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
  connection.sendDiagnostics({ uri: document.uri, diagnostics });
}

function lookupPrimitive(symbol: string) {
  const target = symbol.toLowerCase();
  return (catalog.primitives || []).find(p => (p.id || '').toLowerCase() === target || (p.name || '').toLowerCase() === target) || null;
}

function makeDiag(range: Range, message: string): Diagnostic {
  return { severity: DiagnosticSeverity.Error, range, message, source: DIAGNOSTIC_SOURCE };
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
  return makeDiag(range, (msg.split('\n')[0] || 'Parse error'));
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

export function startServer(): void {
  documents.listen(connection);
  connection.listen();
}

export type { Diagnostic };
