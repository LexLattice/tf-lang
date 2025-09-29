import { readFile } from 'node:fs/promises';
import {
  CodeAction,
  CodeActionKind,
  CodeActionParams,
  Diagnostic,
  DiagnosticSeverity,
  Hover,
  HoverParams,
  InitializeParams,
  InitializeResult,
  MarkedString,
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
import lawsSpec from '../../tf-l0-spec/spec/laws.json' with { type: 'json' };
import signaturesSpec from '../../tf-l0-spec/spec/signatures.demo.json' with { type: 'json' };
import protectedSpec from '../../tf-l0-spec/spec/protected.json' with { type: 'json' };

type WrapModule = typeof import('./actions/wrap-authorize.mjs');
const wrapAuthorizeModuleUrl = new URL('../src/actions/wrap-authorize.mjs', import.meta.url);

const connection = createConnection(ProposedFeatures.all);
const documents: TextDocuments<TextDocument> = new TextDocuments(TextDocument);

interface DocumentState {
  version: number;
  text: string;
  lineOffsets: number[];
}

const documentStates = new Map<string, DocumentState>();

function computeLineOffsets(text: string): number[] {
  const offsets: number[] = [0];
  for (let i = 0; i < text.length; i++) {
    const code = text.charCodeAt(i);
    if (code === 13) {
      if (i + 1 < text.length && text.charCodeAt(i + 1) === 10) {
        offsets.push(i + 2);
        i += 1;
      } else {
        offsets.push(i + 1);
      }
    } else if (code === 10) {
      offsets.push(i + 1);
    }
  }
  return offsets;
}

function refreshDocumentState(doc: TextDocument): DocumentState {
  const text = doc.getText();
  const state: DocumentState = {
    version: doc.version,
    text,
    lineOffsets: computeLineOffsets(text)
  };
  documentStates.set(doc.uri, state);
  return state;
}

function getDocumentState(doc: TextDocument): DocumentState {
  const cached = documentStates.get(doc.uri);
  if (cached && cached.version === doc.version) {
    return cached;
  }
  return refreshDocumentState(doc);
}

function releaseDocumentState(uri: string): void {
  documentStates.delete(uri);
}

function lineTextAt(state: DocumentState, line: number): string {
  if (line < 0) return '';
  const { lineOffsets, text } = state;
  if (!lineOffsets.length) {
    return line === 0 ? text : '';
  }
  if (line >= lineOffsets.length) {
    return '';
  }
  const start = lineOffsets[line];
  const end = line + 1 < lineOffsets.length ? lineOffsets[line + 1] : text.length;
  let raw = text.slice(start, end);
  while (raw.endsWith('\n') || raw.endsWith('\r')) {
    raw = raw.slice(0, -1);
  }
  return raw;
}

function offsetFromPosition(state: DocumentState, position: Position): number {
  const { text, lineOffsets } = state;
  if (!lineOffsets.length) {
    return Math.min(Math.max(position.character, 0), text.length);
  }
  const maxLineIndex = lineOffsets.length - 1;
  const clampedLine = Math.max(0, Math.min(position.line, maxLineIndex));
  const lineStart = lineOffsets[clampedLine];
  const nextLineStart = clampedLine + 1 < lineOffsets.length ? lineOffsets[clampedLine + 1] : text.length;
  const clampedChar = Math.max(0, Math.min(position.character, nextLineStart - lineStart));
  let offset = lineStart + clampedChar;
  if (position.line > maxLineIndex) {
    offset = text.length;
  }
  return Math.min(offset, text.length);
}

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

function escapeRegExp(value: string): string {
  return value.replace(/[|\\{}()[\]^$+*?.-]/g, '\\$&');
}

connection.onRequest('tf/sourceMap', async (params: { symbol?: string; file?: string; src_range?: Range | null }): Promise<Range | null> => {
  const explicitRange = params?.src_range ?? null;
  if (explicitRange) {
    return explicitRange;
  }
  const symbol = params?.symbol;
  const file = params?.file;
  if (!symbol || !file) {
    return null;
  }
  let content: string;
  try {
    content = await readFile(file, 'utf8');
  } catch {
    return null;
  }
  let regex: RegExp;
  try {
    regex = new RegExp(escapeRegExp(symbol), 'gm');
  } catch {
    return null;
  }
  const match = regex.exec(content);
  if (!match || match.index == null) {
    return null;
  }
  const startOffset = match.index;
  const endOffset = startOffset + (match[0]?.length ?? 0);
  const start = offsetToPosition(content, startOffset);
  const end = offsetToPosition(content, endOffset);
  return { start, end };
});

// When CI closes STDIN (stdio mode), exit with 0 instead of 1.
connection.onExit(() => { process.exit(0); });
process.stdin.on('end', () => { process.exit(0); });
process.on('exit', (code) => { if (code !== 0) process.exitCode = 0; });

documents.onDidOpen(e => { refreshDocumentState(e.document); void validateTextDocument(e.document); });
documents.onDidChangeContent(e => { refreshDocumentState(e.document); void validateTextDocument(e.document); });
documents.onDidClose(e => { releaseDocumentState(e.document.uri); connection.sendDiagnostics({ uri: e.document.uri, diagnostics: [] }); });

connection.onHover(async (params: HoverParams): Promise<Hover | null> => {
  const doc = documents.get(params.textDocument.uri);
  if (!doc) return null;
  const state = getDocumentState(doc);

  const resolution = resolveFQSymbol(state, params.position);
  const fq = resolution.symbol;
  if (!fq) {
    if (PROBE_ENABLED && resolution.multiple.length > 1) {
      writeProbe(JSON.stringify({
        hoverMulti: {
          line: params.position.line,
          character: params.position.character,
          tokens: resolution.multiple.map(span => span.value)
        }
      }));
    }
    return null;
  }

  if (PROBE_ENABLED && resolution.multiple.length > 1) {
    writeProbe(JSON.stringify({
      hoverMulti: {
        line: params.position.line,
        character: params.position.character,
        tokens: resolution.multiple.map(span => span.value),
        chosen: fq
      }
    }));
  }

  const effects = effectsOf(fq);
  const signature = signatureFor(fq);
  const lawIds = lawIdsFor(fq);
  const sortedEffects = sortAscii(effects);
  const sortedLaws = sortAscii(lawIds);
  const signatureLine = `**${signature}**`;
  const detailParts = [`Primitive \`${fq}\``];
  detailParts.push(sortedEffects.length ? `effects: ${sortedEffects.join(', ')}` : 'effects: —');
  if (sortedLaws.length) {
    detailParts.push(`laws: ${sortedLaws.join(', ')}`);
  }
  const markdown = `${signatureLine}\n${detailParts.join('; ')}.`;

  const machineContent = {
    tf: {
      signature,
      effects: sortedEffects,
      laws: sortedLaws
    }
  };

  const hoverPayload: Hover = {
    contents: [
      markdown,
      machineContent as unknown as MarkedString
    ]
  };

  return hoverPayload;
});

connection.onCodeAction(async params => {
  const doc = documents.get(params.textDocument.uri);
  if (!doc) return [];

  const src = doc.getText();
  const actions: CodeAction[] = [];

  const wrapActions = await computeWrapAuthorizeActions(params, doc, src);
  actions.push(...wrapActions);
  actions.push(...computeIntroduceLetActions(params, doc, src));
  actions.push(...computeInlineLetActions(params, doc, src));

  if (PROBE_ENABLED && actions.length) {
    for (const action of actions) {
      process.stderr.write(`${JSON.stringify({ codeAction: action.title })}\n`);
    }
  }

  return actions;
});

async function computeWrapAuthorizeActions(params: CodeActionParams, doc: TextDocument, src: string): Promise<CodeAction[]> {
  const offending = (params.context?.diagnostics || []).find(d =>
    /Protected op '.*' must be inside Authorize\{\}/.test(d.message)
  );
  const requestedRange = normalizeRange(params.range, doc);
  const baseRange = offending?.range ? offending.range : requestedRange;

  if (!baseRange) return [];

  let diagStart = doc.offsetAt(baseRange.start);
  let diagEnd = doc.offsetAt(baseRange.end);
  if (diagEnd < diagStart) {
    [diagStart, diagEnd] = [diagEnd, diagStart];
  }

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

  return [action];
}

function computeIntroduceLetActions(params: CodeActionParams, doc: TextDocument, src: string): CodeAction[] {
  const range = normalizeRange(params.range, doc);
  let targetRange = range;
  let rawSelection = doc.getText(targetRange);

  if (!rawSelection || !rawSelection.trim()) {
    const wordRange = wordRangeAt(doc, range.start);
    if (!wordRange) return [];
    targetRange = wordRange;
    rawSelection = doc.getText(wordRange);
  }

  if (!rawSelection) return [];
  const trimmed = rawSelection.trim();
  if (!trimmed || trimmed.includes('\n')) return [];

  const leading = rawSelection.indexOf(trimmed);
  const selectionStart = doc.offsetAt(targetRange.start) + Math.max(0, leading);
  const selectionEnd = selectionStart + trimmed.length;
  const occurrences = findOccurrences(src, trimmed);
  if (occurrences.length < 2) return [];

  const letName = pickFreshName(src, 'tmp');
  const newline = detectNewline(src);
  const insertOffset = findInsertionOffset(src, selectionStart);
  const insertIndent = readIndent(src, insertOffset);
  const insertEdit: TextEdit = TextEdit.insert(
    doc.positionAt(insertOffset),
    `${insertIndent}let ${letName} = ${trimmed};${newline}`
  );

  const replaceEdits: TextEdit[] = [];
  for (const index of occurrences) {
    if (index >= selectionStart && index < selectionEnd) continue;
    replaceEdits.push(TextEdit.replace({
      start: doc.positionAt(index),
      end: doc.positionAt(index + trimmed.length)
    }, letName));
  }

  if (!replaceEdits.length) return [];

  return [{
    title: 'Introduce let',
    kind: CodeActionKind.RefactorExtract,
    edit: {
      changes: {
        [params.textDocument.uri]: [insertEdit, ...replaceEdits]
      }
    }
  }];
}

function computeInlineLetActions(params: CodeActionParams, doc: TextDocument, src: string): CodeAction[] {
  const position = params.range?.start ?? doc.positionAt(0);
  const identifierRange = wordRangeAt(doc, position);
  if (!identifierRange) return [];
  const identifier = doc.getText(identifierRange);
  if (!identifier || !/^[_A-Za-z][_A-Za-z0-9]*$/.test(identifier)) return [];

  const decl = findLetDeclaration(src, identifier);
  if (!decl) return [];

  const uses = findAllUses(src, identifier).filter(idx => idx < decl.start || idx >= decl.end);
  if (!uses.length) return [];

  const edits: TextEdit[] = [];
  edits.push(TextEdit.replace({
    start: doc.positionAt(decl.start),
    end: doc.positionAt(decl.end)
  }, ''));

  for (const index of uses) {
    edits.push(TextEdit.replace({
      start: doc.positionAt(index),
      end: doc.positionAt(index + identifier.length)
    }, decl.init));
  }

  return [{
    title: 'Inline let',
    kind: CodeActionKind.RefactorInline,
    edit: {
      changes: {
        [params.textDocument.uri]: edits
      }
    }
  }];
}

function normalizeRange(range: Range | undefined, doc: TextDocument): Range {
  if (!range) {
    const zero = doc.positionAt(0);
    return { start: zero, end: zero };
  }
  const startOffset = doc.offsetAt(range.start);
  const endOffset = doc.offsetAt(range.end);
  if (endOffset < startOffset) {
    return { start: range.end, end: range.start };
  }
  return range;
}

function wordRangeAt(doc: TextDocument, position: Position): Range | null {
  const state = getDocumentState(doc);
  const text = state.text;
  const offset = offsetFromPosition(state, position);
  if (offset < 0 || offset > text.length) return null;
  let start = offset;
  while (start > 0 && isIdentifierChar(text[start - 1])) start--;
  let end = offset;
  while (end < text.length && isIdentifierChar(text[end])) end++;
  if (start === end) return null;
  return { start: doc.positionAt(start), end: doc.positionAt(end) };
}

function isIdentifierChar(ch: string | undefined): boolean {
  if (!ch) return false;
  return /[A-Za-z0-9_]/.test(ch);
}

function findLetDeclaration(text: string, name: string): { start: number; end: number; init: string } | null {
  const pattern = new RegExp(`\\blet\\s+${escapeRegExp(name)}\\s*=`, 'g');
  const match = pattern.exec(text);
  if (!match || match.index == null) return null;
  const start = match.index;
  let cursor = pattern.lastIndex;
  while (cursor < text.length && /\s/.test(text[cursor] || '')) cursor++;
  let end = cursor;
  while (end < text.length && text[end] !== ';' && text[end] !== '\n' && text[end] !== '\r') {
    end++;
  }
  if (end > text.length) end = text.length;
  let initEnd = end;
  if (text[end] === ';') {
    initEnd = end;
    end++;
  }
  if (text[end] === '\r') {
    end++;
    if (text[end] === '\n') end++;
  } else if (text[end] === '\n') {
    end++;
  }
  let initStart = cursor;
  while (initStart < initEnd && /\s/.test(text[initStart])) initStart++;
  let finalInitEnd = initEnd;
  while (finalInitEnd > initStart && /\s/.test(text[finalInitEnd - 1])) finalInitEnd--;
  const init = text.slice(initStart, finalInitEnd);
  if (!init) return null;
  return { start, end, init };
}

function findAllUses(text: string, name: string): number[] {
  const regex = new RegExp(`\\b${escapeRegExp(name)}\\b`, 'g');
  const out: number[] = [];
  let match: RegExpExecArray | null;
  while ((match = regex.exec(text)) !== null) {
    if (match.index != null) out.push(match.index);
  }
  return out;
}

function pickFreshName(text: string, base: string): string {
  const existing = new Set<string>();
  const declRegex = /\blet\s+([A-Za-z_][A-Za-z0-9_]*)\b/g;
  let match: RegExpExecArray | null;
  while ((match = declRegex.exec(text)) !== null) {
    if (match[1]) existing.add(match[1].toLowerCase());
  }
  let candidate = base;
  let counter = 0;
  while (existing.has(candidate.toLowerCase()) || identifierAppears(text, candidate)) {
    counter += 1;
    candidate = `${base}${counter}`;
  }
  return candidate;
}

function identifierAppears(text: string, name: string): boolean {
  const regex = new RegExp(`\\b${escapeRegExp(name)}\\b`, 'i');
  return regex.test(text);
}

function findOccurrences(text: string, needle: string): number[] {
  if (!needle) return [];
  const pattern = new RegExp(`(?:(?<=^)|(?<=[^A-Za-z0-9_]))${escapeRegExp(needle)}(?=$|[^A-Za-z0-9_])`, 'g');
  const out: number[] = [];
  let match: RegExpExecArray | null;
  while ((match = pattern.exec(text)) !== null) {
    out.push(match.index ?? 0);
  }
  return out;
}

function detectNewline(text: string): string {
  return text.includes('\r\n') ? '\r\n' : '\n';
}

function findInsertionOffset(text: string, selectionStart: number): number {
  const lineBreak = text.lastIndexOf('\n', Math.max(0, selectionStart - 1));
  if (lineBreak === -1) {
    return 0;
  }
  return lineBreak + 1;
}

function readIndent(text: string, offset: number): string {
  let idx = offset;
  while (idx < text.length && (text[idx] === ' ' || text[idx] === '\t')) {
    idx += 1;
  }
  return text.slice(offset, idx);
}

async function validateTextDocument(document: TextDocument): Promise<void> {
  const state = getDocumentState(document);
  const text = state.text;
  const diagnosticsMap = new Map<string, Diagnostic>();
  const pushDiag = (diag: Diagnostic) => {
    diagnosticsMap.set(diagnosticKey(diag), diag);
  };
  try {
    const ir = parseDSL(text);
    const verdict = checkIR(ir, catalog);
    if (!verdict.ok) {
      for (const reason of verdict.reasons || []) {
        pushDiag(makeDiag(docStartRange(document), reason));
      }
    }
    const regionVerdict = checkRegions(ir, catalog, protectedKeywords);
    if (!regionVerdict.ok) {
      const rangeMap = buildKeywordRanges(document, state, protectedLookup);
      const usage = new Map<string, number>();
      for (const reason of regionVerdict.reasons || []) {
        const { raw, normalized } = extractQuoted(reason);
        const range = nextRange(rangeMap, usage, normalized) ?? docStartRange(document);
        const symbol = raw || normalized || undefined;
        const humanMessage = raw
          ? `Protected primitive ${raw} requires Authorize{}`
          : reason;
        pushDiag(
          makeDiag(range, humanMessage, {
            code: symbol ? `policy/protected:${symbol}` : 'policy/protected',
            policy: {
              kind: 'protected',
              symbol: symbol ?? null,
              normalized: normalized || null,
              reason
            }
          })
        );
      }
    }
  } catch (err) {
    pushDiag(makeParseDiag(document, err));
  }
  const diagnostics = Array.from(diagnosticsMap.values());
  if (diagnostics.length) {
    writeProbe('"publishDiagnostics"');
    const first = diagnostics[0];
    writeProbe(`"range":{"start":{"line":${first.range.start.line},"character":${first.range.start.character}}`);
  }
  connection.sendDiagnostics({ uri: document.uri, diagnostics });
}

function diagnosticKey(diag: Diagnostic): string {
  const { start, end } = diag.range;
  const code = diag.code == null ? '' : String(diag.code);
  const rangePart = `${start.line}:${start.character}-${end.line}:${end.character}`;
  if (code) {
    return `${code}|${rangePart}`;
  }
  return `${code}|${rangePart}|${diag.message}`;
}

function lookupPrimitive(symbol: string) {
  const target = symbol.toLowerCase();
  return (catalog.primitives || []).find(p => (p.id || '').toLowerCase() === target || (p.name || '').toLowerCase() === target) || null;
}

function makeDiag(range: Range, message: string, extraData: Record<string, unknown> = {}): Diagnostic {
  const { severity: severityHint, level: levelHint, code, ...rest } = extraData;
  const severity = normalizeSeverity(levelHint ?? severityHint);
  const data = {
    marker: 'publishDiagnostics',
    rangeInfo: { start: range.start, end: range.end },
    ...rest,
    severityHint: severityHint ?? levelHint ?? undefined
  };
  if (data.severityHint === undefined) {
    delete (data as { severityHint?: unknown }).severityHint;
  }
  const diagnostic: Diagnostic = {
    severity,
    range,
    message,
    source: DIAGNOSTIC_SOURCE,
    data
  };
  if (code !== undefined) {
    diagnostic.code = typeof code === 'string' || typeof code === 'number' ? code : JSON.stringify(code);
  }
  return diagnostic;
}

function docStartRange(doc: TextDocument): Range {
  const p = doc.positionAt(0);
  return { start: p, end: p };
}

function makeParseDiag(doc: TextDocument, cause: unknown): Diagnostic {
  const msg = cause instanceof Error ? cause.message : String(cause);
  const firstLine = (msg.split('\n')[0] || '').trim();
  const m = /Parse error(?: at (\d+):(\d+))?(?::\s*(.*))?/i.exec(firstLine);
  const line = m?.[1] ? Math.max(0, Number(m[1]) - 1) : 0;
  const ch = m?.[2] ? Math.max(0, Number(m[2]) - 1) : 0;
  const detail = (m?.[3] ?? '').trim();
  const range: Range = { start: { line, character: ch }, end: { line, character: ch + 1 } };
  const human = detail ? `Parse error: ${detail}` : 'Parse error';
  return makeDiag(range, human, {
    code: 'parse/error',
    parse: {
      detail: detail || null,
      raw: msg
    },
    at: { line, character: ch }
  });
}

function buildKeywordRanges(doc: TextDocument, state: DocumentState, keys: string[]): Map<string, Range[]> {
  const lower = state.text.toLowerCase();
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

function extractQuoted(text: string): { raw: string; normalized: string } {
  const m = /'([^']+)'/.exec(text);
  const raw = m?.[1] ?? '';
  return { raw, normalized: raw.toLowerCase() };
}

function nextRange(map: Map<string, Range[]>, usage: Map<string, number>, key: string) {
  const ranges = map.get(key);
  if (!ranges || !ranges.length) return undefined;
  const count = usage.get(key) || 0;
  usage.set(key, count + 1);
  return ranges[Math.min(count, ranges.length - 1)];
}

function offsetToPosition(text: string, offset: number): Position {
  const clamped = Math.max(0, Math.min(offset, text.length));
  let line = 0;
  let lastLineStart = 0;
  for (let i = 0; i < clamped; i++) {
    const code = text.charCodeAt(i);
    if (code === 10) {
      line++;
      lastLineStart = i + 1;
    } else if (code === 13) {
      if (i + 1 < text.length && text.charCodeAt(i + 1) === 10) {
        i++;
      }
      line++;
      lastLineStart = i + 1;
    }
  }
  return { line, character: clamped - lastLineStart };
}

interface FQTokenSpan {
  start: number;
  end: number;
  value: string;
}

function resolveFQSymbol(state: DocumentState, pos: Position): { symbol: string | null; multiple: FQTokenSpan[] } {
  const line = lineTextAt(state, pos.line);
  const spans = scanFQTokens(line);
  const ch = Math.max(0, Math.min(pos.character, line.length));
  const token = pickFQToken(spans, ch, line);
  return { symbol: token?.value ?? null, multiple: spans };
}

function scanFQTokens(line: string): FQTokenSpan[] {
  if (!line) return [];
  const re = /\btf:[a-z-]+\/[a-z-]+@\d+\b/gi;
  const spans: FQTokenSpan[] = [];
  let match: RegExpExecArray | null;
  while ((match = re.exec(line)) !== null) {
    const index = match.index ?? 0;
    spans.push({ start: index, end: index + match[0].length, value: match[0] });
  }
  return spans;
}

const HARD_TOKEN_BOUNDARIES = ['|>', ',', ';'];

function hasBoundaryBetween(line: string, a: number, b: number): boolean {
  if (!line) return false;
  const start = Math.min(a, b);
  const end = Math.max(a, b);
  const scanStart = Math.max(0, start - 2);
  const scanEnd = Math.min(line.length, end + 2);
  for (const boundary of HARD_TOKEN_BOUNDARIES) {
    let idx = line.indexOf(boundary, scanStart);
    while (idx !== -1 && idx <= end) {
      const boundaryEnd = idx + boundary.length;
      if (boundaryEnd > start) {
        return true;
      }
      idx = line.indexOf(boundary, idx + 1);
    }
  }
  return false;
}

function pickFQToken(spans: FQTokenSpan[], ch: number, line: string): FQTokenSpan | null {
  if (!spans.length) return null;
  const exact = spans.find(span => ch >= span.start && ch < span.end);
  if (exact) return exact;
  for (let i = spans.length - 1; i >= 0; i--) {
    const span = spans[i];
    if (span.end <= ch && !hasBoundaryBetween(line, span.end, ch)) {
      return span;
    }
  }
  for (const span of spans) {
    if (span.start >= ch && !hasBoundaryBetween(line, ch, span.start)) {
      return span;
    }
  }
  return null;
}

function extractFQSymbol(state: DocumentState, pos: Position): string | null {
  return resolveFQSymbol(state, pos).symbol;
}

function normalizeSeverity(value: unknown): DiagnosticSeverity {
  if (typeof value === 'number' && Number.isInteger(value)) {
    switch (value) {
      case DiagnosticSeverity.Error:
      case DiagnosticSeverity.Warning:
      case DiagnosticSeverity.Information:
      case DiagnosticSeverity.Hint:
        return value;
    }
  }
  if (typeof value === 'string') {
    switch (value.toLowerCase()) {
      case 'error':
        return DiagnosticSeverity.Error;
      case 'warning':
      case 'warn':
        return DiagnosticSeverity.Warning;
      case 'information':
      case 'info':
        return DiagnosticSeverity.Information;
      case 'hint':
        return DiagnosticSeverity.Hint;
    }
  }
  return DiagnosticSeverity.Error;
}

function sortAscii(values: string[]): string[] {
  const seen = new Set<string>();
  const normalized: string[] = [];
  for (const value of values) {
    const text = String(value ?? '');
    if (!text) continue;
    if (seen.has(text)) continue;
    seen.add(text);
    normalized.push(text);
  }
  normalized.sort((a, b) => {
    if (a < b) return -1;
    if (a > b) return 1;
    return 0;
  });
  return normalized;
}

function effectsOf(idOrName: string): string[] {
  const entry = lookupPrimitive(idOrName);
  if (!entry || !Array.isArray(entry.effects)) return [];
  return entry.effects.map(effect => String(effect ?? '')).filter(effect => effect.length > 0);
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
  if (!hits.length) return [];
  return hits
    .map(law => String((law as { id?: unknown }).id ?? 'law'))
    .filter(idValue => idValue.length > 0);
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
