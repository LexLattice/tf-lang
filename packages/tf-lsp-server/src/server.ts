/// <reference path="./shims.d.ts" />
import {
  CodeAction,
  CodeActionKind,
  CodeActionParams,
  Diagnostic,
  DiagnosticSeverity,
  Hover,
  InitializeParams,
  InitializeResult,
  Position,
  ProposedFeatures,
  Range,
  TextDocumentChangeEvent,
  TextDocumentPositionParams,
  TextDocumentSyncKind,
  TextDocuments,
  createConnection,
} from 'vscode-languageserver/node.js';
import { TextDocument } from 'vscode-languageserver-textdocument';
import { readFile } from 'node:fs/promises';
import { dirname, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';

interface CatalogPrimitive {
  id?: string;
  name?: string;
  effects?: string[];
  domain?: string;
  major?: number;
}

interface Catalog {
  primitives?: CatalogPrimitive[];
}

interface CheckVerdict {
  ok: boolean;
  reasons?: string[];
}

interface RegionVerdict {
  ok: boolean;
  reasons?: string[];
}

interface TextRange {
  start: number;
  end: number;
}

interface ProtectedMatch {
  keyword: string;
  index: number;
  length: number;
}

type ParseFn = (source: string) => unknown;
type CheckFn = (ir: unknown, catalog: Catalog) => CheckVerdict;
type RegionFn = (ir: unknown, catalog: Catalog, protectedKeywords: string[]) => RegionVerdict;
interface LawEntry {
  id: string;
  applies_to?: string[];
}

const connection = createConnection(ProposedFeatures.all);
const documents: TextDocuments<TextDocument> = new TextDocuments(TextDocument);
const protectedMatchesByUri = new Map<string, ProtectedMatch[]>();

const moduleDir = dirname(fileURLToPath(import.meta.url));
const repoRoot = resolve(moduleDir, '../../..');
const catalogPath = resolve(repoRoot, 'packages/tf-l0-spec/spec/catalog.json');
const protectedPath = resolve(repoRoot, 'packages/tf-l0-spec/spec/protected.json');
const lawsPath = resolve(repoRoot, 'packages/tf-l0-spec/spec/laws.json');
const parserModuleUrl = new URL('../../tf-compose/src/parser.mjs', import.meta.url);
const checkModuleUrl = new URL('../../tf-l0-check/src/check.mjs', import.meta.url);
const regionModuleUrl = new URL('../../tf-l0-check/src/regions.mjs', import.meta.url);

let catalogCache: Catalog | null = null;
let protectedKeywordsCache: string[] | null = null;
let lawsCache: LawEntry[] | null = null;
let parseFnPromise: Promise<ParseFn> | null = null;
let checkFnPromise: Promise<CheckFn> | null = null;
let regionFnPromise: Promise<RegionFn> | null = null;

connection.onInitialize((params: InitializeParams): InitializeResult => {
  const capabilities = params.capabilities;
  void capabilities;

  return {
    capabilities: {
      textDocumentSync: TextDocumentSyncKind.Incremental,
      hoverProvider: true,
      codeActionProvider: true,
    },
  };
});

documents.onDidOpen((event: TextDocumentChangeEvent<TextDocument>) => {
  void validateDocument(event.document);
});

documents.onDidChangeContent((change: TextDocumentChangeEvent<TextDocument>) => {
  void validateDocument(change.document);
});

documents.onDidClose((event) => {
  protectedMatchesByUri.delete(event.document.uri);
  connection.sendDiagnostics({ uri: event.document.uri, diagnostics: [] });
});

connection.onHover(async (params: TextDocumentPositionParams): Promise<Hover | null> => {
  const document = documents.get(params.textDocument.uri);
  if (!document) {
    return null;
  }
  const symbol = extractSymbol(document, params.position);
  if (!symbol) {
    return null;
  }
  const catalog = await loadCatalog();
  const primitive = lookupPrimitive(catalog, symbol);
  if (!primitive) {
    return null;
  }
  const signature = buildSignature(primitive);
  const effects = primitive.effects ?? [];
  const laws = await loadLawIds(primitive.id ?? '');
  const payload = JSON.stringify({ signature, effects, laws });
  return { contents: { kind: 'plaintext', value: payload } };
});

connection.onCodeAction((params: CodeActionParams): CodeAction[] => {
  const document = documents.get(params.textDocument.uri);
  if (!document) {
    return [];
  }
  const matches = protectedMatchesByUri.get(document.uri);
  if (!matches || matches.length === 0) {
    return [];
  }
  const text = document.getText();
  const actions: CodeAction[] = [];
  for (const match of matches) {
    const callRange = expandToCall(text, match);
    const range = rangeFromOffsets(document, callRange.start, callRange.end);
    const editText = buildAuthorizeWrap(document, text, callRange);
    const action: CodeAction = {
      title: `Wrap ${match.keyword} with Authorize`,
      kind: CodeActionKind.QuickFix,
      edit: {
        changes: {
          [document.uri]: [
            {
              range,
              newText: editText,
            },
          ],
        },
      },
    };
    actions.push(action);
  }
  return actions;
});

documents.listen(connection);
connection.listen();

async function validateDocument(document: TextDocument): Promise<void> {
  const text = document.getText();

  try {
    const ir = await parseText(text);
    const [catalog, protectedKeywords] = await Promise.all([
      loadCatalog(),
      loadProtectedKeywords(),
    ]);

    const diagnostics: Diagnostic[] = [];

    const checkVerdict = await runCheckIR(ir, catalog);
    if (Array.isArray(checkVerdict.reasons)) {
      for (const reason of checkVerdict.reasons) {
        diagnostics.push({
          severity: DiagnosticSeverity.Warning,
          message: reason,
          range: fullDocumentRange(document),
        });
      }
    }

    const regionVerdict = await runCheckRegions(ir, catalog, protectedKeywords);
    if (!regionVerdict.ok) {
      const matches = findProtectedViolations(text, protectedKeywords);
      protectedMatchesByUri.set(document.uri, matches);
      for (const match of matches) {
        diagnostics.push({
          severity: DiagnosticSeverity.Error,
          message: `Protected op '${match.keyword}' must be inside Authorize{}`,
          range: rangeForMatch(document, match.index, match.length),
        });
      }
    } else {
      protectedMatchesByUri.delete(document.uri);
    }

    connection.sendDiagnostics({ uri: document.uri, diagnostics });
  } catch (error: unknown) {
    const parseDiagnostic = buildParseDiagnostic(error, document);
    if (parseDiagnostic) {
      protectedMatchesByUri.delete(document.uri);
      connection.sendDiagnostics({ uri: document.uri, diagnostics: [parseDiagnostic] });
      return;
    }
    const message = error instanceof Error && typeof error.message === 'string'
      ? error.message
      : 'Unknown error during validation';
    connection.console.error(message);
    protectedMatchesByUri.delete(document.uri);
    connection.sendDiagnostics({ uri: document.uri, diagnostics: [] });
  }
}

async function loadCatalog(): Promise<Catalog> {
  if (catalogCache) {
    return catalogCache;
  }
  try {
    const raw = await readFile(catalogPath, 'utf8');
    catalogCache = JSON.parse(raw) as Catalog;
  } catch (error) {
    connection.console.error(`Failed to load catalog: ${String(error)}`);
    catalogCache = { primitives: [] };
  }
  return catalogCache;
}

async function loadProtectedKeywords(): Promise<string[]> {
  if (protectedKeywordsCache) {
    return protectedKeywordsCache;
  }
  try {
    const raw = await readFile(protectedPath, 'utf8');
    const parsed = JSON.parse(raw) as { protected_keywords?: string[] };
    protectedKeywordsCache = parsed.protected_keywords ?? [];
  } catch (error) {
    connection.console.error(`Failed to load protected keywords: ${String(error)}`);
    protectedKeywordsCache = [];
  }
  return protectedKeywordsCache;
}

async function loadLawIds(primitiveId: string): Promise<string[]> {
  if (!primitiveId) {
    return [];
  }
  if (!lawsCache) {
    try {
      const raw = await readFile(lawsPath, 'utf8');
      const parsed = JSON.parse(raw) as { laws?: LawEntry[] };
      lawsCache = parsed.laws ?? [];
    } catch (error) {
      connection.console.error(`Failed to load laws: ${String(error)}`);
      lawsCache = [];
    }
  }
  return lawsCache
    .filter((law) => Array.isArray(law.applies_to) && law.applies_to.some((entry) => entry?.toLowerCase() === primitiveId.toLowerCase()))
    .map((law) => law.id)
    .filter((id) => typeof id === 'string' && id.length > 0);
}

async function parseText(source: string): Promise<unknown> {
  if (!parseFnPromise) {
    parseFnPromise = import(parserModuleUrl.href).then((mod) => {
      const fn = (mod as { parseDSL?: ParseFn }).parseDSL;
      if (typeof fn !== 'function') {
        throw new Error('parseDSL export missing');
      }
      return fn;
    });
  }
  const fn = await parseFnPromise;
  return fn(source);
}

async function runCheckIR(ir: unknown, catalog: Catalog): Promise<CheckVerdict> {
  if (!checkFnPromise) {
    checkFnPromise = import(checkModuleUrl.href).then((mod) => {
      const fn = (mod as { checkIR?: CheckFn }).checkIR;
      if (typeof fn !== 'function') {
        throw new Error('checkIR export missing');
      }
      return fn;
    });
  }
  const fn = await checkFnPromise;
  return fn(ir, catalog);
}

async function runCheckRegions(
  ir: unknown,
  catalog: Catalog,
  protectedKeywords: string[],
): Promise<RegionVerdict> {
  if (!regionFnPromise) {
    regionFnPromise = import(regionModuleUrl.href).then((mod) => {
      const fn = (mod as { checkRegions?: RegionFn }).checkRegions;
      if (typeof fn !== 'function') {
        throw new Error('checkRegions export missing');
      }
      return fn;
    });
  }
  const fn = await regionFnPromise;
  return fn(ir, catalog, protectedKeywords);
}

function lookupPrimitive(catalog: Catalog, symbol: string): CatalogPrimitive | null {
  const primitives = catalog.primitives ?? [];
  const lowerSymbol = symbol.toLowerCase();
  if (lowerSymbol.startsWith('tf:')) {
    return primitives.find((entry) => (entry.id ?? '').toLowerCase() === lowerSymbol) ?? null;
  }
  return (
    primitives.find((entry) => (entry.name ?? '').toLowerCase() === lowerSymbol) ??
    primitives.find((entry) => (entry.id ?? '').toLowerCase().endsWith(`/${lowerSymbol}@${entry.major ?? ''}`)) ??
    null
  );
}

function buildSignature(primitive: CatalogPrimitive): string {
  const name = primitive.name ?? primitive.id ?? 'unknown';
  const hints: Record<string, string> = {
    publish: 'topic, key, payload',
    'write-object': 'resource_uri, payload',
    'read-object': 'resource_uri',
    'sign-data': 'key_ref, payload',
  };
  const lowerName = typeof name === 'string' ? name.toLowerCase() : 'op';
  const hint = hints[lowerName] ?? '';
  return hint.length > 0 ? `${name}(${hint})` : `${name}()`;
}

function extractSymbol(document: TextDocument, position: Position): string | null {
  const text = document.getText();
  const offset = document.offsetAt(position);
  if (offset < 0 || offset >= text.length) {
    return null;
  }
  const isSymbolChar = (ch: string) => /[A-Za-z0-9_:@\/-]/.test(ch);
  let start = offset;
  while (start > 0 && isSymbolChar(text[start - 1] ?? '')) {
    start -= 1;
  }
  let end = offset;
  while (end < text.length && isSymbolChar(text[end] ?? '')) {
    end += 1;
  }
  const symbol = text.slice(start, end).trim();
  return symbol.length > 0 ? symbol : null;
}

function buildParseDiagnostic(error: unknown, document: TextDocument): Diagnostic | null {
  if (!(error instanceof Error) || typeof error.message !== 'string') {
    return null;
  }
  const match = /Parse error at (\d+):(\d+):([^\n]+)/.exec(error.message);
  if (!match) {
    return null;
  }
  const line = Math.max(parseInt(match[1], 10) - 1, 0);
  const character = Math.max(parseInt(match[2], 10) - 1, 0);
  const start: Position = { line, character };
  const end: Position = { line, character: character + 1 };
  return {
    severity: DiagnosticSeverity.Error,
    message: error.message.trim(),
    range: { start, end },
  };
}

function fullDocumentRange(document: TextDocument): Range {
  const endPosition = document.positionAt(document.getText().length);
  return { start: { line: 0, character: 0 }, end: endPosition };
}

function rangeForMatch(document: TextDocument, index: number, length: number): Range {
  const start = document.positionAt(index);
  const end = document.positionAt(index + length);
  return { start, end };
}

function rangeFromOffsets(document: TextDocument, start: number, end: number): Range {
  const startPos = document.positionAt(start);
  const endPos = document.positionAt(end);
  return { start: startPos, end: endPos };
}

function findProtectedViolations(text: string, keywords: string[]): ProtectedMatch[] {
  if (keywords.length === 0) {
    return [];
  }
  const authorizeRanges = collectAuthorizeRanges(text);
  const matches: ProtectedMatch[] = [];
  for (const keyword of keywords) {
    const regex = new RegExp(`\\b${escapeRegExp(keyword)}\\b`, 'gi');
    let match: RegExpExecArray | null = null;
    while ((match = regex.exec(text)) !== null) {
      const index = match.index;
      const length = match[0].length;
      if (!insideAuthorize(index, authorizeRanges)) {
        matches.push({ keyword, index, length });
      }
    }
  }
  return matches;
}

function expandToCall(text: string, match: ProtectedMatch): TextRange {
  let start = match.index;
  let end = match.index + match.length;
  let cursor = end;
  while (cursor < text.length && /\s/.test(text[cursor] ?? '')) {
    cursor += 1;
  }
  if (cursor < text.length && text[cursor] === '(') {
    const close = findMatchingSymbol(text, cursor, '(', ')');
    if (close !== -1) {
      end = close + 1;
    }
  }
  return { start, end };
}

function buildAuthorizeWrap(document: TextDocument, text: string, range: TextRange): string {
  const original = text.slice(range.start, range.end);
  const startPos = document.positionAt(range.start);
  const lineStartOffset = document.offsetAt({ line: startPos.line, character: 0 });
  const leadingSegment = text.slice(lineStartOffset, range.start);
  const indentMatch = leadingSegment.match(/^\s*/);
  const indent = indentMatch ? indentMatch[0] ?? '' : '';
  const inner = original.trim();
  const innerLines = inner.split(/\r?\n/).map((line) => line.trim());
  const indented = innerLines.map((line) => `${indent}  ${line}`).join('\n');
  return `Authorize{ scope: "" } {\n${indented}\n${indent}}`;
}

function collectAuthorizeRanges(text: string): TextRange[] {
  const ranges: TextRange[] = [];
  const lower = text.toLowerCase();
  let index = 0;
  while (index < lower.length) {
    const hit = lower.indexOf('authorize', index);
    if (hit === -1) {
      break;
    }
    let cursor = hit + 'authorize'.length;
    cursor = skipWhitespace(lower, cursor);
    if (cursor < lower.length && lower[cursor] === '(') {
      const endParen = findMatchingSymbol(text, cursor, '(', ')');
      if (endParen === -1) {
        index = hit + 1;
        continue;
      }
      cursor = endParen + 1;
    }
    cursor = skipWhitespace(lower, cursor);
    if (cursor >= lower.length || lower[cursor] !== '{') {
      index = hit + 1;
      continue;
    }
    const endBrace = findMatchingSymbol(text, cursor, '{', '}');
    if (endBrace === -1) {
      index = hit + 1;
      continue;
    }
    ranges.push({ start: cursor, end: endBrace + 1 });
    index = hit + 1;
  }
  return ranges;
}

function skipWhitespace(text: string, start: number): number {
  let cursor = start;
  while (cursor < text.length && /\s/.test(text[cursor] ?? '')) {
    cursor += 1;
  }
  return cursor;
}

function findMatchingSymbol(text: string, start: number, openChar: string, closeChar: string): number {
  let depth = 0;
  let inString: string | null = null;
  for (let i = start; i < text.length; i += 1) {
    const ch = text[i];
    if (inString) {
      if (ch === '\\' && i + 1 < text.length) {
        i += 1;
        continue;
      }
      if (ch === inString) {
        inString = null;
      }
      continue;
    }
    if (ch === '"' || ch === '\'') {
      inString = ch;
      continue;
    }
    if (ch === openChar) {
      depth += 1;
    } else if (ch === closeChar) {
      depth -= 1;
      if (depth === 0) {
        return i;
      }
    }
  }
  return -1;
}

function insideAuthorize(index: number, ranges: TextRange[]): boolean {
  return ranges.some((range) => index >= range.start && index < range.end);
}

function escapeRegExp(input: string): string {
  return input.replace(/[.*+?^${}()|[\]\\]/g, '\\$&');
}
