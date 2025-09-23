/// <reference path="./shims.d.ts" />

import {
  CodeActionParams,
  Connection,
  Diagnostic,
  DiagnosticSeverity,
  Hover,
  HoverParams,
  InitializeParams,
  InitializeResult,
  Position,
  ProposedFeatures,
  Range,
  TextDocumentSyncKind,
  TextDocuments,
  createConnection,
} from 'vscode-languageserver/node.js';
import { TextDocument } from 'vscode-languageserver-textdocument';
import catalogData from '../../tf-l0-spec/spec/catalog.json' with { type: 'json' };
import lawsData from '../../tf-l0-spec/spec/laws.json' with { type: 'json' };
import protectedData from '../../tf-l0-spec/spec/protected.json' with { type: 'json' };
import { parseDSL } from 'tf-compose/parser';
import { checkIR } from 'tf-l0/check';
import { checkRegions } from 'tf-l0/regions';

type CatalogPrimitive = {
  id?: string;
  name?: string;
  effects?: string[];
};

type CatalogSpec = {
  primitives?: CatalogPrimitive[];
};

type ProtectedSpec = {
  protected_keywords?: string[];
};

type LawEntry = {
  id?: string;
  applies_to?: string[];
};

type LawsSpec = {
  laws?: LawEntry[];
};

const catalog: CatalogSpec = catalogData;
const laws: LawsSpec = lawsData;
const protectedSpec: ProtectedSpec = protectedData;
const protectedKeywords: string[] = Array.isArray(protectedSpec.protected_keywords)
  ? protectedSpec.protected_keywords.map((keyword) => keyword.toLowerCase())
  : [];

const primitiveById = new Map<string, CatalogPrimitive>();
const primitiveByName = new Map<string, CatalogPrimitive>();

for (const entry of Array.isArray(catalog.primitives) ? catalog.primitives : []) {
  if (!entry) {
    continue;
  }
  const id = typeof entry.id === 'string' ? entry.id : null;
  const name = typeof entry.name === 'string' ? entry.name : null;
  if (id) {
    primitiveById.set(id.toLowerCase(), entry);
  }
  if (name) {
    primitiveByName.set(name.toLowerCase(), entry);
  }
}

const connection: Connection = createConnection(ProposedFeatures.all);
const documents: TextDocuments<TextDocument> = new TextDocuments(TextDocument);

documents.onDidOpen((event) => {
  void validateTextDocument(event.document);
});

documents.onDidChangeContent((change) => {
  void validateTextDocument(change.document);
});

documents.onDidClose((event) => {
  connection.sendDiagnostics({ uri: event.document.uri, diagnostics: [] });
});

connection.onInitialize((_params: InitializeParams): InitializeResult => {
  const capabilities: InitializeResult = {
    capabilities: {
      textDocumentSync: {
        openClose: true,
        change: TextDocumentSyncKind.Incremental,
      },
      hoverProvider: true,
      codeActionProvider: true,
    },
  };

  return capabilities;
});

connection.onInitialized(() => {
  // No-op for now.
});

connection.onHover((params: HoverParams): Hover | null => {
  const document = documents.get(params.textDocument.uri);
  if (!document) {
    return null;
  }

  const symbol = extractSymbol(document, params.position);
  if (!symbol) {
    return null;
  }

  const primitive = findPrimitive(symbol);
  if (!primitive) {
    return null;
  }

  const effects = toStringArray(primitive.entry.effects);
  const lawsForPrimitive = findLawsFor(primitive.id);
  const signature = buildSignature(symbol, primitive.entry);
  const markdown = createHoverMarkdown(signature, effects, lawsForPrimitive);

  return {
    contents: {
      kind: 'markdown',
      value: markdown,
    },
  };
});

connection.onCodeAction((_params: CodeActionParams) => {
  return [];
});

documents.listen(connection);
connection.listen();

async function validateTextDocument(textDocument: TextDocument): Promise<void> {
  const diagnostics: Diagnostic[] = [];
  const text = textDocument.getText();

  try {
    const ir = parseDSL(text);
    const policyVerdict = checkIR(ir, catalog);
    if (policyVerdict && policyVerdict.reasons && policyVerdict.reasons.length > 0) {
      for (const reason of policyVerdict.reasons) {
        diagnostics.push({
          severity: DiagnosticSeverity.Error,
          range: fullDocumentRange(textDocument),
          message: reason,
          source: 'tf-lsp',
        });
      }
    }

    const regionVerdict = checkRegions(ir, catalog, protectedKeywords);
    if (!regionVerdict.ok) {
      for (const reason of regionVerdict.reasons) {
        const token = extractToken(reason);
        const range = token ? findTokenRange(textDocument, text, token) : fullDocumentRange(textDocument);
        diagnostics.push({
          severity: DiagnosticSeverity.Error,
          range,
          message: reason,
          source: 'tf-lsp',
        });
      }
    }
  } catch (error) {
    const message = error instanceof Error ? error.message : String(error);
    const range = rangeFromParseError(textDocument, message);
    diagnostics.push({
      severity: DiagnosticSeverity.Error,
      range,
      message,
      source: 'tf-lsp',
    });
  }

  connection.sendDiagnostics({ uri: textDocument.uri, diagnostics });
}

function fullDocumentRange(textDocument: TextDocument): Range {
  const end = textDocument.positionAt(textDocument.getText().length);
  return { start: { line: 0, character: 0 }, end };
}

function extractToken(reason: string): string | null {
  const match = /'([^']+)'/.exec(reason);
  return match ? match[1] : null;
}

function findTokenRange(textDocument: TextDocument, content: string, token: string): Range {
  const lowerContent = content.toLowerCase();
  const lowerToken = token.toLowerCase();
  const index = lowerContent.indexOf(lowerToken);
  if (index === -1) {
    return fullDocumentRange(textDocument);
  }

  const start = textDocument.positionAt(index);
  const end = textDocument.positionAt(index + token.length);
  return { start, end };
}

function rangeFromParseError(textDocument: TextDocument, message: string): Range {
  const match = /Parse error at (\d+):(\d+)/.exec(message);
  if (!match) {
    return fullDocumentRange(textDocument);
  }

  const line = Math.max(0, Number.parseInt(match[1], 10) - 1);
  const character = Math.max(0, Number.parseInt(match[2], 10) - 1);
  const start: Position = { line, character };
  const end: Position = { line, character: character + 1 };
  return { start, end };
}

function extractSymbol(textDocument: TextDocument, position: Position): string | null {
  const content = textDocument.getText();
  const offset = textDocument.offsetAt(position);
  if (offset < 0 || offset > content.length) {
    return null;
  }

  let start = offset;
  while (start > 0 && isSymbolChar(content[start - 1])) {
    start -= 1;
  }

  let end = offset;
  while (end < content.length && isSymbolChar(content[end])) {
    end += 1;
  }

  if (start === end) {
    return null;
  }

  return content.slice(start, end);
}

function isSymbolChar(ch: string): boolean {
  return /[A-Za-z0-9_:@\-/]/.test(ch);
}

function findPrimitive(symbol: string): { id: string; entry: CatalogPrimitive } | null {
  const normalized = symbol.toLowerCase();
  if (/^tf:[a-z0-9_-]+\/[a-z0-9_-]+@\d+$/.test(normalized)) {
    const entry = primitiveById.get(normalized);
    if (entry) {
      const id = typeof entry.id === 'string' ? entry.id : symbol;
      return { id, entry };
    }
  }

  const entryByName = primitiveByName.get(normalized);
  if (entryByName) {
    const id = typeof entryByName.id === 'string' ? entryByName.id : symbol;
    return { id, entry: entryByName };
  }

  return null;
}

function buildSignature(symbol: string, entry: CatalogPrimitive): string {
  const displayName = typeof entry.name === 'string' && entry.name.length > 0 ? entry.name : symbol;
  return `${displayName}(...)`;
}

function createHoverMarkdown(signature: string, effects: string[], lawsForPrimitive: string[]): string {
  const lines = ['```tf', signature, '```'];
  lines.push('', effects.length > 0 ? `**Effects:** ${effects.join(', ')}` : '**Effects:** (none)');
  lines.push('', lawsForPrimitive.length > 0 ? `**Laws:** ${lawsForPrimitive.join(', ')}` : '**Laws:** (none)');
  return lines.join('\n');
}

function findLawsFor(id: string): string[] {
  const normalized = id.toLowerCase();
  const results: string[] = [];
  for (const law of Array.isArray(laws.laws) ? laws.laws : []) {
    if (!law) {
      continue;
    }
    const appliesTo = Array.isArray(law.applies_to) ? law.applies_to : [];
    const matches = appliesTo.some((target) => typeof target === 'string' && target.toLowerCase() === normalized);
    if (matches && typeof law.id === 'string') {
      results.push(law.id);
    }
  }
  return results;
}

function toStringArray(values: unknown): string[] {
  if (!Array.isArray(values)) {
    return [];
  }
  return values.filter((value): value is string => typeof value === 'string');
}
