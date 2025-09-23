import {
  createConnection,
  ProposedFeatures,
  TextDocuments,
  TextDocumentSyncKind,
  DiagnosticSeverity,
  type Diagnostic,
  type Hover,
  type Position,
} from 'vscode-languageserver/node.js';
import type { InitializeParams, InitializeResult } from 'vscode-languageserver/node.js';
import { TextDocument } from 'vscode-languageserver-textdocument';
import path from 'node:path';
import { readFile } from 'node:fs/promises';
import { fileURLToPath } from 'node:url';

const connection = createConnection(ProposedFeatures.all);
const documents: TextDocuments<TextDocument> = new TextDocuments(TextDocument);

const moduleDirectory = path.dirname(fileURLToPath(import.meta.url));
const SPEC_DIR = path.resolve(moduleDirectory, '..', '..', 'tf-l0-spec', 'spec');

connection.onInitialize((_params: InitializeParams): InitializeResult => ({
  capabilities: {
    textDocumentSync: TextDocumentSyncKind.Incremental,
  },
}));

documents.listen(connection);
connection.listen();

const PROTECTED_OPERATIONS = new Set(['sign-data', 'write-object']);

type FlowNode = {
  node?: string;
  kind?: string;
  prim?: string;
  children?: FlowNode[] | null;
};

type ParseOutcome =
  | { ast: FlowNode | FlowNode[] }
  | { error: { line: number; column: number; message: string } };

documents.onDidOpen((event) => {
  void validateTextDocument(event.document);
});

documents.onDidChangeContent((change) => {
  void validateTextDocument(change.document);
});

connection.onHover(async (params): Promise<Hover | null> => {
  const document = documents.get(params.textDocument.uri);
  if (!document) {
    return null;
  }

  const primitiveId = extractPrimitiveId(document, params.position);
  if (!primitiveId) {
    return null;
  }

  const [catalogData, lawsData, signaturesData] = await Promise.all([
    loadCatalogData(),
    loadLawsData(),
    loadSignaturesData(),
  ]);

  const effects = extractEffects(catalogData, primitiveId);
  const laws = extractLawIds(lawsData, primitiveId);
  const signature = extractSignature(signaturesData, primitiveId);

  const payload = {
    signature: signature ?? null,
    effects,
    laws,
  };

  const markdown = `\`\`\`json\n${JSON.stringify(payload, null, 2)}\n\`\`\``;
  return { contents: { kind: 'markdown', value: markdown } };
});

async function validateTextDocument(document: TextDocument): Promise<void> {
  const text = document.getText();
  const diagnostics: Diagnostic[] = [];
  const parseOutcome = await safeParse(text);

  if ('error' in parseOutcome) {
    diagnostics.push(createParseDiagnostic(document, parseOutcome.error));
  } else {
    const violations = findProtectedViolations(parseOutcome.ast);
    diagnostics.push(...createProtectionDiagnostics(document, text, violations));
  }

  connection.sendDiagnostics({ uri: document.uri, diagnostics });
}

type FlowParser = (source: string) => unknown;
let cachedParser: FlowParser | null = null;

async function loadParser(): Promise<FlowParser> {
  if (cachedParser) {
    return cachedParser;
  }
  const module = (await import(new URL('../../tf-compose/src/parser.mjs', import.meta.url).href)) as {
    parseDSL?: FlowParser;
  };
  if (typeof module.parseDSL !== 'function') {
    throw new Error('Failed to load TF parser');
  }
  cachedParser = module.parseDSL;
  return cachedParser;
}

async function safeParse(source: string): Promise<ParseOutcome> {
  try {
    const parser = await loadParser();
    const ast = parser(source) as FlowNode | FlowNode[];
    return { ast };
  } catch (error) {
    const message = error instanceof Error ? error.message : String(error);
    const match = /Parse error at (\d+):(\d+)/.exec(message);
    const line = match ? Number.parseInt(match[1], 10) : 1;
    const column = match ? Number.parseInt(match[2], 10) : 1;
    return {
      error: {
        line,
        column,
        message,
      },
    };
  }
}

function createParseDiagnostic(document: TextDocument, info: { line: number; column: number; message: string }): Diagnostic {
  const line = Math.max(0, info.line - 1);
  const character = Math.max(0, info.column - 1);
  const start = { line, character };
  const startOffset = document.offsetAt(start);
  const end = document.positionAt(Math.min(startOffset + 1, document.getText().length));
  return {
    severity: DiagnosticSeverity.Error,
    range: { start, end },
    message: info.message,
    source: 'tf-lsp',
  };
}

function createProtectionDiagnostics(document: TextDocument, text: string, names: readonly string[]): Diagnostic[] {
  if (names.length === 0) {
    return [];
  }

  const diagnostics: Diagnostic[] = [];
  const lowerText = text.toLowerCase();
  const searchOffsets = new Map<string, number>();

  for (const name of names) {
    const lowerName = name.toLowerCase();
    const fromIndex = searchOffsets.get(lowerName) ?? 0;
    const matchIndex = lowerText.indexOf(lowerName, fromIndex);
    if (matchIndex === -1) {
      continue;
    }
    searchOffsets.set(lowerName, matchIndex + lowerName.length);
    const start = document.positionAt(matchIndex);
    const end = document.positionAt(matchIndex + lowerName.length);
    diagnostics.push({
      severity: DiagnosticSeverity.Error,
      range: { start, end },
      message: `Protected operation '${name}' must be wrapped in Authorize{}`,
      source: 'tf-lsp',
    });
  }

  return diagnostics;
}

function findProtectedViolations(root: FlowNode | FlowNode[]): string[] {
  const violations: string[] = [];
  const regionStack: string[] = [];

  const visit = (value: unknown): void => {
    if (Array.isArray(value)) {
      for (const item of value) {
        visit(item);
      }
      return;
    }

    if (!isFlowNode(value)) {
      return;
    }

    const nodeKind = value.node ?? '';
    if (nodeKind === 'Region') {
      const regionKind = typeof value.kind === 'string' ? value.kind : '';
      if (regionKind) {
        regionStack.push(regionKind);
      }
      if (Array.isArray(value.children)) {
        for (const child of value.children) {
          visit(child);
        }
      }
      if (regionKind) {
        regionStack.pop();
      }
      return;
    }

    if (nodeKind === 'Prim') {
      const name = typeof value.prim === 'string' ? value.prim : '';
      if (name && PROTECTED_OPERATIONS.has(name.toLowerCase()) && !regionStack.includes('Authorize')) {
        violations.push(name);
      }
      return;
    }

    if (Array.isArray(value.children)) {
      for (const child of value.children) {
        visit(child);
      }
    }
  };

  visit(root);
  return violations;
}

function isFlowNode(value: unknown): value is FlowNode {
  if (value === null || typeof value !== 'object') {
    return false;
  }
  const candidate = value as FlowNode;
  if (candidate.node !== undefined && typeof candidate.node !== 'string') {
    return false;
  }
  if (candidate.kind !== undefined && typeof candidate.kind !== 'string') {
    return false;
  }
  if (candidate.prim !== undefined && typeof candidate.prim !== 'string') {
    return false;
  }
  if (candidate.children !== undefined && !Array.isArray(candidate.children)) {
    return false;
  }
  return true;
}

function extractPrimitiveId(document: TextDocument, position: Position): string | null {
  const text = document.getText();
  const offset = document.offsetAt(position);
  if (offset < 0 || offset > text.length) {
    return null;
  }

  const isIdentifierChar = (ch: string): boolean => /[A-Za-z0-9_:@/\-]/.test(ch);

  let start = offset;
  while (start > 0 && isIdentifierChar(text[start - 1])) {
    start -= 1;
  }
  let end = offset;
  while (end < text.length && isIdentifierChar(text[end])) {
    end += 1;
  }

  if (start === end) {
    return null;
  }

  const candidate = text.slice(start, end);
  if (/^tf:[a-z0-9-]+\/[a-z0-9-]+@\d+$/i.test(candidate)) {
    return candidate.toLowerCase();
  }
  return null;
}

let cachedCatalogData: unknown | undefined;
async function loadCatalogData(): Promise<unknown> {
  if (cachedCatalogData === undefined) {
    cachedCatalogData = await readJsonFile('catalog.json');
  }
  return cachedCatalogData;
}

let cachedLawsData: unknown | undefined;
async function loadLawsData(): Promise<unknown> {
  if (cachedLawsData === undefined) {
    cachedLawsData = await readJsonFile('laws.json');
  }
  return cachedLawsData;
}

let cachedSignaturesData: unknown | undefined;
async function loadSignaturesData(): Promise<unknown> {
  if (cachedSignaturesData === undefined) {
    cachedSignaturesData = await readJsonFile('signatures.demo.json');
  }
  return cachedSignaturesData;
}

async function readJsonFile(name: string): Promise<unknown> {
  try {
    const raw = await readFile(path.join(SPEC_DIR, name), 'utf8');
    return JSON.parse(raw) as unknown;
  } catch {
    return null;
  }
}

function extractEffects(catalog: unknown, id: string): string[] {
  if (!catalog || typeof catalog !== 'object') {
    return [];
  }
  const primitives = (catalog as { primitives?: unknown }).primitives;
  if (!Array.isArray(primitives)) {
    return [];
  }
  for (const entry of primitives) {
    if (!entry || typeof entry !== 'object') {
      continue;
    }
    const candidate = entry as { id?: unknown; effects?: unknown };
    if (candidate.id === id) {
      const effects = candidate.effects;
      if (Array.isArray(effects)) {
        return effects.filter((effect): effect is string => typeof effect === 'string');
      }
      break;
    }
  }
  return [];
}

function extractLawIds(lawsData: unknown, id: string): string[] {
  if (!lawsData || typeof lawsData !== 'object') {
    return [];
  }
  const laws = (lawsData as { laws?: unknown }).laws;
  if (!Array.isArray(laws)) {
    return [];
  }
  const matches: string[] = [];
  for (const law of laws) {
    if (!law || typeof law !== 'object') {
      continue;
    }
    const record = law as { id?: unknown; applies_to?: unknown };
    const applies = Array.isArray(record.applies_to)
      ? record.applies_to.filter((value): value is string => typeof value === 'string')
      : [];
    if (applies.includes(id)) {
      const lawId = record.id;
      if (typeof lawId === 'string') {
        matches.push(lawId);
      }
    }
  }
  return matches;
}

function extractSignature(signatures: unknown, id: string): unknown | null {
  if (!signatures || typeof signatures !== 'object') {
    return null;
  }
  if (Object.prototype.hasOwnProperty.call(signatures, id)) {
    const record = signatures as Record<string, unknown>;
    return record[id] ?? null;
  }
  return null;
}
