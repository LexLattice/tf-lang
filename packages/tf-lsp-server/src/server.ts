import {
  createConnection,
  Diagnostic,
  DiagnosticSeverity,
  InitializeParams,
  MarkupKind,
  ProposedFeatures,
  TextDocumentSyncKind,
  TextDocuments
} from 'vscode-languageserver/node';
import { TextDocument } from 'vscode-languageserver-textdocument';
import { promises as fs } from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';

const connection = createConnection(ProposedFeatures.all);
const documents: TextDocuments<TextDocument> = new TextDocuments(TextDocument);
const parserModulePromise = import('../../tf-compose/src/parser.mjs') as Promise<{
  parseDSL: (source: string) => unknown;
}>;

const PROTECTED_NAMES = new Set(['sign-data', 'write-object']);
const moduleDir = path.dirname(fileURLToPath(import.meta.url));
const specDir = path.resolve(moduleDir, '../../tf-l0-spec/spec');
const catalogPath = path.join(specDir, 'catalog.json');
const lawsPath = path.join(specDir, 'laws.json');
const signaturesPath = path.join(specDir, 'signatures.demo.json');
const hoverDataPromise = loadHoverData();

type OperationInfo = {
  name: string;
  violation: boolean;
};

documents.onDidOpen((event) => {
  void validateTextDocument(event.document);
});

documents.onDidChangeContent((change) => {
  void validateTextDocument(change.document);
});

documents.onDidClose((event) => {
  connection.sendDiagnostics({ uri: event.document.uri, diagnostics: [] });
});

connection.onHover(async (params) => {
  const document = documents.get(params.textDocument.uri);
  if (!document) {
    return null;
  }

  const payload = await buildHoverPayload(document, params.position);
  if (!payload) {
    return null;
  }

  const markdown = ['```json', JSON.stringify(payload, null, 2), '```'].join('\n');
  return {
    contents: {
      kind: MarkupKind.Markdown,
      value: markdown
    }
  };
});

connection.onInitialize((_params: InitializeParams) => ({
  capabilities: {
    textDocumentSync: TextDocumentSyncKind.Incremental
  }
}));

documents.listen(connection);
connection.listen();

async function validateTextDocument(document: TextDocument): Promise<void> {
  const diagnostics: Diagnostic[] = [];
  const text = document.getText();

  try {
    const { parseDSL } = await parserModulePromise;
    const ast = parseDSL(text);
    diagnostics.push(...collectProtectedDiagnostics(text, document, ast));
  } catch (error) {
    const diagnostic = createParseDiagnostic(error, document);
    if (diagnostic) {
      diagnostics.push(diagnostic);
    } else {
      connection.console.error(`parse failure: ${String(error)}`);
    }
  }

  connection.sendDiagnostics({ uri: document.uri, diagnostics });
}

function createParseDiagnostic(error: unknown, document: TextDocument): Diagnostic | null {
  const message = error instanceof Error ? error.message : String(error);
  const match = /Parse error at (\d+):(\d+)/.exec(message);
  let rangeStart = { line: 0, character: 0 };
  if (match) {
    const line = Math.max(parseInt(match[1], 10) - 1, 0);
    const character = Math.max(parseInt(match[2], 10) - 1, 0);
    rangeStart = { line, character };
  }
  const start = clampPosition(rangeStart, document);
  const end = document.positionAt(document.offsetAt(start) + 1);
  return {
    severity: DiagnosticSeverity.Error,
    range: { start, end },
    message,
    source: 'tf-lsp'
  };
}

function clampPosition(position: { line: number; character: number }, document: TextDocument) {
  const totalLines = document.lineCount;
  const line = Math.min(Math.max(position.line, 0), Math.max(totalLines - 1, 0));
  const lineText = document.getText({
    start: { line, character: 0 },
    end: { line, character: Number.MAX_SAFE_INTEGER }
  });
  const maxCharacter = Math.max(lineText.length - 1, 0);
  const character = Math.min(Math.max(position.character, 0), maxCharacter);
  return { line, character };
}

function collectProtectedDiagnostics(text: string, document: TextDocument, ast: unknown): Diagnostic[] {
  const operations = collectOperations(ast, []);
  const diagnostics: Diagnostic[] = [];
  let searchIndex = 0;

  for (const operation of operations) {
    const pattern = new RegExp(`\\b${escapeRegex(operation.name)}\\b`, 'g');
    pattern.lastIndex = searchIndex;
    const match = pattern.exec(text);
    if (!match) {
      searchIndex = text.length;
      continue;
    }

    if (operation.violation) {
      const start = document.positionAt(match.index);
      const end = document.positionAt(match.index + operation.name.length);
      diagnostics.push({
        severity: DiagnosticSeverity.Error,
        range: { start, end },
        message: `Protected operation '${operation.name}' must be wrapped in Authorize{}`,
        source: 'tf-lsp'
      });
    }

    searchIndex = match.index + operation.name.length;
  }

  return diagnostics;
}

type HoverPayload = {
  signature: unknown;
  effects: string[];
  laws: string[];
};

async function buildHoverPayload(
  document: TextDocument,
  position: { line: number; character: number }
): Promise<HoverPayload | null> {
  const offset = document.offsetAt(position);
  const text = document.getText();
  const primitiveId = findPrimitiveAtOffset(text, offset);
  if (!primitiveId) {
    return null;
  }

  const data = await hoverDataPromise;
  const primitive = data.primitives.get(primitiveId);
  if (!primitive) {
    return null;
  }

  const signature = data.signatures.get(primitiveId) ?? null;
  const laws = data.laws.get(primitiveId) ?? [];
  const effects = Array.isArray(primitive.effects) ? primitive.effects : [];
  return { signature, effects, laws };
}

function findPrimitiveAtOffset(text: string, offset: number): string | null {
  const regex = /tf:[a-z0-9-]+\/[a-z0-9-]+@[0-9]+/gi;
  let match: RegExpExecArray | null;
  while ((match = regex.exec(text)) !== null) {
    const start = match.index;
    const end = start + match[0].length;
    if (offset >= start && offset <= end) {
      return match[0].toLowerCase();
    }
  }
  return null;
}

type HoverData = {
  primitives: Map<string, { effects?: string[] }>;
  laws: Map<string, string[]>;
  signatures: Map<string, unknown>;
};

async function loadHoverData(): Promise<HoverData> {
  const primitives = new Map<string, { effects?: string[] }>();
  const laws = new Map<string, string[]>();
  const signatures = new Map<string, unknown>();

  try {
    const catalogRaw = await fs.readFile(catalogPath, 'utf8');
    const catalogJson = JSON.parse(catalogRaw);
    if (Array.isArray(catalogJson?.primitives)) {
      for (const entry of catalogJson.primitives) {
        if (!entry) {
          continue;
        }
        const id = normalizePrimitiveId(entry.id);
        if (!id) {
          continue;
        }
        const effects = Array.isArray(entry.effects)
          ? entry.effects.filter((value: unknown): value is string => typeof value === 'string')
          : [];
        primitives.set(id, { effects });
      }
    }
  } catch (error) {
    connection.console.error(`hover catalog load failed: ${String(error)}`);
  }

  try {
    const lawsRaw = await fs.readFile(lawsPath, 'utf8');
    const lawsJson = JSON.parse(lawsRaw);
    if (Array.isArray(lawsJson?.laws)) {
      for (const entry of lawsJson.laws) {
        if (!entry || typeof entry.id !== 'string' || !Array.isArray(entry.applies_to)) {
          continue;
        }
        for (const target of entry.applies_to) {
          const id = normalizePrimitiveId(target);
          if (!id) {
            continue;
          }
          const list = laws.get(id) ?? [];
          list.push(entry.id);
          laws.set(id, list);
        }
      }
    }
  } catch (error) {
    connection.console.error(`hover laws load failed: ${String(error)}`);
  }

  try {
    const signaturesRaw = await fs.readFile(signaturesPath, 'utf8');
    const signaturesJson = JSON.parse(signaturesRaw);
    if (signaturesJson && typeof signaturesJson === 'object') {
      for (const [id, value] of Object.entries(signaturesJson as Record<string, unknown>)) {
        const normalized = normalizePrimitiveId(id);
        if (!normalized) {
          continue;
        }
        signatures.set(normalized, value);
      }
    }
  } catch (error) {
    if ((error as NodeJS.ErrnoException)?.code !== 'ENOENT') {
      connection.console.error(`hover signatures load failed: ${String(error)}`);
    }
  }

  return { primitives, laws, signatures };
}

function normalizePrimitiveId(value: unknown): string | null {
  return typeof value === 'string' ? value.toLowerCase() : null;
}

function collectOperations(node: unknown, regionStack: string[]): OperationInfo[] {
  const results: OperationInfo[] = [];
  visit(node, regionStack, results);
  return results;
}

function visit(node: unknown, regionStack: string[], out: OperationInfo[]): void {
  if (node == null) {
    return;
  }

  if (Array.isArray(node)) {
    for (const entry of node) {
      visit(entry, regionStack, out);
    }
    return;
  }

  if (typeof node !== 'object') {
    return;
  }

  const typedNode = node as { [key: string]: unknown };
  const kind = typeof typedNode.kind === 'string' ? typedNode.kind : '';

  if (typedNode.node === 'Region') {
    const nextStack = kind ? regionStack.concat([kind]) : regionStack.slice();
    visit(typedNode.children, nextStack, out);
    return;
  }

  if (typedNode.node === 'Prim') {
    const name = typeof typedNode.prim === 'string' ? typedNode.prim.toLowerCase() : '';
    if (name.length > 0) {
      const violation = PROTECTED_NAMES.has(name) && !regionStack.includes('Authorize');
      out.push({ name, violation });
    }
    return;
  }

  visit(typedNode.children, regionStack, out);
}

function escapeRegex(value: string): string {
  return value.replace(/[.*+?^${}()|[\]\\]/g, '\\$&');
}
