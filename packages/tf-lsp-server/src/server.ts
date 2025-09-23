import {
  createConnection,
  ProposedFeatures,
  InitializeParams,
  TextDocuments,
  TextDocumentSyncKind,
  Diagnostic,
  DiagnosticSeverity,
  Range
} from "vscode-languageserver/node";
import type { Hover, HoverParams } from "vscode-languageserver/node";
import { TextDocument } from "vscode-languageserver-textdocument";
import { readFile } from "node:fs/promises";
import path from "node:path";
import { fileURLToPath, pathToFileURL } from "node:url";

type ParseFunction = (source: string) => FlowNode;

type FlowNode = {
  node?: string;
  kind?: string;
  prim?: string;
  children?: FlowNode[];
};

interface CatalogPrimitive {
  id: string;
  effects: string[];
}

const connection = createConnection(ProposedFeatures.all);
const documents = new TextDocuments(TextDocument);

const currentFile = fileURLToPath(import.meta.url);
const currentDir = path.dirname(currentFile);
const parserUrl = pathToFileURL(
  path.resolve(currentDir, "../..", "tf-compose", "src", "parser.mjs")
).href;
const protectedPath = path.resolve(
  currentDir,
  "../..",
  "tf-l0-spec",
  "spec",
  "protected.json"
);
const catalogPath = path.resolve(
  currentDir,
  "../..",
  "tf-l0-spec",
  "spec",
  "catalog.json"
);
const lawsPath = path.resolve(
  currentDir,
  "../..",
  "tf-l0-spec",
  "spec",
  "laws.json"
);
const signaturesPath = path.resolve(
  currentDir,
  "../..",
  "tf-l0-spec",
  "spec",
  "signatures.demo.json"
);

let parsePromise: Promise<ParseFunction> | undefined;
let protectedKeywordsPromise: Promise<string[]> | undefined;
let catalogPromise: Promise<Map<string, CatalogPrimitive>> | undefined;
let lawPromise: Promise<Map<string, string[]>> | undefined;
let signaturePromise: Promise<Map<string, unknown>> | undefined;

connection.onInitialize((_params: InitializeParams) => ({
  capabilities: {
    textDocumentSync: TextDocumentSyncKind.Incremental
  }
}));

documents.onDidOpen((event) => {
  void validateTextDocument(event.document);
});

documents.onDidChangeContent((change) => {
  void validateTextDocument(change.document);
});

documents.onDidClose((event) => {
  connection.sendDiagnostics({ uri: event.document.uri, diagnostics: [] });
});

connection.onHover(async (params: HoverParams): Promise<Hover | undefined> => {
  const document = documents.get(params.textDocument.uri);
  if (!document) {
    return undefined;
  }
  const text = document.getText();
  const offset = document.offsetAt(params.position);
  const primitiveId = findPrimitiveIdentifier(text, offset);
  if (!primitiveId) {
    return undefined;
  }
  const [catalog, laws, signatures] = await Promise.all([
    loadCatalog(),
    loadLaws(),
    loadSignatures()
  ]);
  const catalogEntry = catalog.get(primitiveId);
  if (!catalogEntry) {
    return undefined;
  }
  const signatureValue = signatures.get(primitiveId);
  const hoverPayload = {
    signature: formatSignature(signatureValue),
    effects: catalogEntry.effects,
    laws: laws.get(primitiveId) ?? []
  };
  return {
    contents: {
      kind: "markdown",
      value: ["```json", JSON.stringify(hoverPayload, null, 2), "```"]
        .join("\n")
    }
  };
});

documents.listen(connection);
connection.listen();

async function validateTextDocument(document: TextDocument): Promise<void> {
  const diagnostics: Diagnostic[] = [];
  const text = document.getText();
  let root: FlowNode | undefined;

  try {
    const parseDSL = await loadParser();
    root = parseDSL(text);
  } catch (error) {
    const diagnostic = createParseDiagnostic(error, document);
    if (diagnostic) {
      diagnostics.push(diagnostic);
    }
    connection.sendDiagnostics({ uri: document.uri, diagnostics });
    return;
  }

  const protectedKeywords = await loadProtectedKeywords();
  const violations = collectProtectedViolations(root, protectedKeywords);
  if (violations.length > 0) {
    const rangeMap = buildRangeMap(violations, text, document);
    for (const violation of violations) {
      const range = takeRange(violation, rangeMap);
      if (!range) {
        continue;
      }
      diagnostics.push({
        range,
        severity: DiagnosticSeverity.Error,
        source: "tf-lsp",
        message: `Protected op '${violation}' must be inside Authorize{}`
      });
    }
  }

  connection.sendDiagnostics({ uri: document.uri, diagnostics });
}

async function loadParser(): Promise<ParseFunction> {
  if (!parsePromise) {
    parsePromise = import(parserUrl).then((mod) => {
      if (!isParseModule(mod)) {
        throw new Error("parser.mjs missing parseDSL export");
      }
      return mod.parseDSL;
    });
  }
  return parsePromise;
}

async function loadProtectedKeywords(): Promise<string[]> {
  if (!protectedKeywordsPromise) {
    protectedKeywordsPromise = readFile(protectedPath, "utf8")
      .then((contents) => {
        const parsed = safeJsonParse(contents);
        return extractProtectedList(parsed);
      })
      .catch(() => []);
  }
  return protectedKeywordsPromise;
}

async function loadCatalog(): Promise<Map<string, CatalogPrimitive>> {
  if (!catalogPromise) {
    catalogPromise = readFile(catalogPath, "utf8")
      .then((contents) => extractCatalogMap(safeJsonParse(contents)))
      .catch(() => new Map());
  }
  return catalogPromise;
}

async function loadLaws(): Promise<Map<string, string[]>> {
  if (!lawPromise) {
    lawPromise = readFile(lawsPath, "utf8")
      .then((contents) => extractLawMap(safeJsonParse(contents)))
      .catch(() => new Map());
  }
  return lawPromise;
}

async function loadSignatures(): Promise<Map<string, unknown>> {
  if (!signaturePromise) {
    signaturePromise = readFile(signaturesPath, "utf8")
      .then((contents) => extractSignatureMap(safeJsonParse(contents)))
      .catch(() => new Map());
  }
  return signaturePromise;
}

function safeJsonParse(text: string): unknown {
  try {
    return JSON.parse(text);
  } catch {
    return undefined;
  }
}

function extractProtectedList(value: unknown): string[] {
  if (typeof value !== "object" || value === null) {
    return [];
  }
  const maybeKeywords = (value as { protected_keywords?: unknown }).protected_keywords;
  if (!Array.isArray(maybeKeywords)) {
    return [];
  }
  return maybeKeywords.filter((item): item is string => typeof item === "string");
}

function extractCatalogMap(value: unknown): Map<string, CatalogPrimitive> {
  const map = new Map<string, CatalogPrimitive>();
  if (typeof value !== "object" || value === null) {
    return map;
  }
  const primitives = (value as { primitives?: unknown }).primitives;
  if (!Array.isArray(primitives)) {
    return map;
  }
  for (const entry of primitives) {
    if (typeof entry !== "object" || entry === null) {
      continue;
    }
    const id = (entry as { id?: unknown }).id;
    if (typeof id !== "string") {
      continue;
    }
    const effectsValue = (entry as { effects?: unknown }).effects;
    const effects = Array.isArray(effectsValue)
      ? effectsValue.filter((effect): effect is string => typeof effect === "string")
      : [];
    map.set(id, { id, effects });
  }
  return map;
}

function extractLawMap(value: unknown): Map<string, string[]> {
  const map = new Map<string, string[]>();
  if (typeof value !== "object" || value === null) {
    return map;
  }
  const laws = (value as { laws?: unknown }).laws;
  if (!Array.isArray(laws)) {
    return map;
  }
  for (const entry of laws) {
    if (typeof entry !== "object" || entry === null) {
      continue;
    }
    const lawId = (entry as { id?: unknown }).id;
    const applies = (entry as { applies_to?: unknown }).applies_to;
    if (typeof lawId !== "string" || !Array.isArray(applies)) {
      continue;
    }
    for (const primitive of applies) {
      if (typeof primitive !== "string") {
        continue;
      }
      const existing = map.get(primitive) ?? [];
      existing.push(lawId);
      map.set(primitive, existing);
    }
  }
  return map;
}

function extractSignatureMap(value: unknown): Map<string, unknown> {
  const map = new Map<string, unknown>();
  if (typeof value !== "object" || value === null) {
    return map;
  }
  const entries = Object.entries(value as Record<string, unknown>);
  for (const [key, signature] of entries) {
    if (typeof key === "string") {
      map.set(key, signature);
    }
  }
  return map;
}

function collectProtectedViolations(root: FlowNode | undefined, protectedKeywords: string[]): string[] {
  if (!root) {
    return [];
  }
  const results: string[] = [];
  const lowerKeywords = protectedKeywords.map((item) => item.toLowerCase());

  const visit = (node: FlowNode | undefined, authorizeDepth: boolean): void => {
    if (!node) {
      return;
    }
    if (node.node === "Region") {
      const nextAuthorize = authorizeDepth || (node.kind ?? "").toLowerCase() === "authorize";
      for (const child of node.children ?? []) {
        visit(child, nextAuthorize);
      }
      return;
    }
    if (node.node === "Prim") {
      const name = node.prim ?? "";
      if (name.length > 0) {
        const lowerName = name.toLowerCase();
        const isProtected = lowerKeywords.some((keyword) => keyword.length > 0 && lowerName.includes(keyword));
        if (isProtected && !authorizeDepth) {
          results.push(name);
        }
      }
    }
    for (const child of node.children ?? []) {
      visit(child, authorizeDepth);
    }
  };

  visit(root, false);
  return results;
}

function buildRangeMap(tokens: string[], text: string, document: TextDocument): Map<string, Range[]> {
  const map = new Map<string, Range[]>();
  const uniqueTokens = Array.from(new Set(tokens));
  for (const token of uniqueTokens) {
    map.set(token, findTokenRanges(token, text, document));
  }
  return map;
}

function findTokenRanges(token: string, text: string, document: TextDocument): Range[] {
  if (token.length === 0) {
    return [];
  }
  const ranges: Range[] = [];
  const pattern = new RegExp(escapeForRegExp(token), "g");
  let match: RegExpExecArray | null;
  while ((match = pattern.exec(text)) !== null) {
    const start = document.positionAt(match.index);
    const end = document.positionAt(match.index + match[0].length);
    ranges.push({ start, end });
    if (pattern.lastIndex === match.index) {
      pattern.lastIndex += 1;
    }
  }
  return ranges;
}

function takeRange(token: string, map: Map<string, Range[]>): Range | undefined {
  const ranges = map.get(token);
  if (!ranges || ranges.length === 0) {
    return undefined;
  }
  return ranges.shift();
}

function escapeForRegExp(value: string): string {
  return value.replace(/[.*+?^${}()|[\]\\]/g, "\\$&");
}

function createParseDiagnostic(error: unknown, document: TextDocument): Diagnostic | undefined {
  const message = extractMessage(error);
  if (!message) {
    return undefined;
  }
  const firstLine = message.split("\n")[0] ?? message;
  const match = /Parse error at (\d+):(\d+)/.exec(firstLine);
  if (!match) {
    return undefined;
  }
  const line = Number.parseInt(match[1] ?? "", 10) - 1;
  const character = Number.parseInt(match[2] ?? "", 10) - 1;
  if (Number.isNaN(line) || Number.isNaN(character)) {
    return undefined;
  }
  const start = {
    line: Math.max(0, line),
    character: Math.max(0, character)
  };
  const startOffset = document.offsetAt(start);
  const end = document.positionAt(startOffset + 1);
  return {
    range: { start, end },
    severity: DiagnosticSeverity.Error,
    source: "tf-lsp",
    message: firstLine
  };
}

function extractMessage(error: unknown): string | undefined {
  if (typeof error === "string") {
    return error;
  }
  if (error && typeof error === "object" && "message" in error) {
    const maybeMessage = (error as { message?: unknown }).message;
    if (typeof maybeMessage === "string") {
      return maybeMessage;
    }
  }
  return undefined;
}

function isParseModule(value: unknown): value is { parseDSL: ParseFunction } {
  if (typeof value !== "object" || value === null) {
    return false;
  }
  const maybeFunction = (value as { parseDSL?: unknown }).parseDSL;
  return typeof maybeFunction === "function";
}

function findPrimitiveIdentifier(text: string, offset: number): string | undefined {
  const pattern = /tf:[A-Za-z0-9_-]+\/[A-Za-z0-9_-]+@[0-9]+/g;
  let match: RegExpExecArray | null;
  while ((match = pattern.exec(text)) !== null) {
    const start = match.index;
    const end = start + match[0].length;
    if (offset >= start && offset <= end) {
      return match[0];
    }
  }
  return undefined;
}

function formatSignature(value: unknown): string {
  if (value === undefined) {
    return "(signature unavailable)";
  }
  try {
    return JSON.stringify(value, null, 2);
  } catch {
    return "(signature unavailable)";
  }
}
