import {
  CodeAction,
  CodeActionParams,
  createConnection,
  Diagnostic,
  DiagnosticSeverity,
  Hover,
  HoverParams,
  InitializeParams,
  InitializeResult,
  ProposedFeatures,
  TextDocuments,
  TextDocumentSyncKind,
} from 'vscode-languageserver/node.js';
import { TextDocument } from 'vscode-languageserver-textdocument';
import { readFile } from 'node:fs/promises';

type CatalogEntry = {
  id?: string;
  name?: string;
  domain?: string;
  major?: number;
  effects?: string[];
  keys?: Array<{ name?: string }>;
};

type Catalog = { primitives?: CatalogEntry[] };

type PrimRecord = {
  name: string;
  offending: boolean;
};

type ParserModule = {
  parseDSL: (source: string) => unknown;
};

type CheckModule = {
  checkIR: (ir: unknown, catalog: unknown, options?: unknown) => {
    ok: boolean;
    reasons?: string[];
  };
};

type RegionsModule = {
  checkRegions: (ir: unknown, catalog: unknown, protectedList?: string[]) => {
    ok: boolean;
    reasons?: string[];
  };
};

type Toolkit = {
  parseDSL: ParserModule['parseDSL'];
  checkIR: CheckModule['checkIR'];
  checkRegions: RegionsModule['checkRegions'];
};

type Law = {
  id?: string;
  applies_to?: string[];
};

const connection = createConnection(ProposedFeatures.all);
const documents: TextDocuments<TextDocument> = new TextDocuments(TextDocument);

let cachedCatalog: Catalog | null = null;
let cachedProtected: string[] | null = null;
let toolkitPromise: Promise<Toolkit> | null = null;
let cachedLaws: Law[] | null = null;

connection.onInitialize((_params: InitializeParams): InitializeResult => ({
  capabilities: {
    textDocumentSync: TextDocumentSyncKind.Incremental,
    hoverProvider: true,
    codeActionProvider: true,
  },
}));

documents.onDidOpen(event => {
  void validateTextDocument(event.document);
});

documents.onDidChangeContent(change => {
  void validateTextDocument(change.document);
});

documents.onDidClose(event => {
  connection.sendDiagnostics({ uri: event.document.uri, diagnostics: [] });
});

connection.onHover(async (params: HoverParams): Promise<Hover | null> => {
  const document = documents.get(params.textDocument.uri);
  if (!document) return null;
  const symbol = extractSymbol(document, params.position);
  if (!symbol) return null;

  const catalog = await loadCatalog();
  const entry = resolveCatalogEntry(catalog, symbol);
  if (!entry) return null;

  const effects = Array.isArray(entry.effects) ? entry.effects : [];
  const laws = await loadLaws();
  const matchingLaws = laws
    .filter(law => (law.applies_to || []).includes(entry.id || ''))
    .map(law => law.id)
    .filter((id): id is string => Boolean(id));

  const signature = buildSignature(entry, symbol);
  const sections = [
    '```tf',
    signature,
    '```',
  ];
  if (effects.length) {
    sections.push(`**Effects:** ${effects.join(', ')}`);
  }
  if (matchingLaws.length) {
    sections.push(`**Laws:** ${matchingLaws.join(', ')}`);
  }
  if (entry.id) {
    const entryId = entry.id;
    if (!sections.some(line => line.includes(entryId))) {
      sections.push(`ID: ${entryId}`);
    }
  }

  return {
    contents: {
      kind: 'markdown',
      value: sections.join('\n\n'),
    },
  };
});

connection.onCodeAction((_params: CodeActionParams): CodeAction[] => []);

void documents.listen(connection);
connection.listen();

async function getToolkit(): Promise<Toolkit> {
  if (!toolkitPromise) {
    const parserUrl = new URL('../../tf-compose/src/parser.mjs', import.meta.url).href;
    const checkUrl = new URL('../../tf-l0-check/src/check.mjs', import.meta.url).href;
    const regionsUrl = new URL('../../tf-l0-check/src/regions.mjs', import.meta.url).href;
    toolkitPromise = Promise.all([
      import(parserUrl) as Promise<ParserModule>,
      import(checkUrl) as Promise<CheckModule>,
      import(regionsUrl) as Promise<RegionsModule>,
    ]).then(([parserMod, checkMod, regionsMod]) => ({
      parseDSL: parserMod.parseDSL,
      checkIR: checkMod.checkIR,
      checkRegions: regionsMod.checkRegions,
    }));
  }
  return toolkitPromise;
}

async function validateTextDocument(document: TextDocument): Promise<void> {
  const diagnostics: Diagnostic[] = [];
  const text = document.getText();

  if (!text.trim()) {
    connection.sendDiagnostics({ uri: document.uri, diagnostics });
    return;
  }

  const toolkit = await getToolkit();
  let ir: unknown;
  try {
    ir = toolkit.parseDSL(text);
  } catch (err) {
    diagnostics.push(buildParseDiagnostic(err, document));
    connection.sendDiagnostics({ uri: document.uri, diagnostics });
    return;
  }

  const catalog = await loadCatalog();
  const protectedKeywords = await loadProtected();

  const policyVerdict = toolkit.checkIR(ir, catalog);
  if (!policyVerdict.ok) {
    for (const reason of policyVerdict.reasons || []) {
      diagnostics.push({
        severity: DiagnosticSeverity.Warning,
        message: reason,
        source: 'tf-policy',
        range: {
          start: { line: 0, character: 0 },
          end: document.positionAt(text.length),
        },
      });
    }
  }

  const regionVerdict = toolkit.checkRegions(ir, catalog, protectedKeywords);
  if (!regionVerdict.ok) {
    const prims = collectPrimRecords(ir, protectedKeywords);
    diagnostics.push(...createProtectedDiagnostics(prims, document));
    const surfaced = diagnostics.filter(d => d.message.includes('Protected op')).length;
    if (surfaced < (regionVerdict.reasons || []).length) {
      for (const reason of (regionVerdict.reasons || []).slice(surfaced)) {
        diagnostics.push({
          severity: DiagnosticSeverity.Error,
          message: reason,
          source: 'tf-policy',
          range: {
            start: { line: 0, character: 0 },
            end: document.positionAt(text.length),
          },
        });
      }
    }
  }

  connection.sendDiagnostics({ uri: document.uri, diagnostics });
}

function buildParseDiagnostic(err: unknown, document: TextDocument): Diagnostic {
  const message = err instanceof Error ? err.message : String(err);
  const match = /Parse error at (\d+):(\d+)/.exec(message);
  const line = match ? Number(match[1]) - 1 : 0;
  const character = match ? Number(match[2]) - 1 : 0;
  return {
    severity: DiagnosticSeverity.Error,
    message,
    source: 'tf-parser',
    range: {
      start: { line: Math.max(line, 0), character: Math.max(character, 0) },
      end: { line: Math.max(line, 0), character: Math.max(character + 1, 0) },
    },
  };
}

async function loadCatalog(): Promise<Catalog> {
  if (cachedCatalog) return cachedCatalog;
  const candidates = [
    new URL('../../tf-l0-spec/spec/catalog.json', import.meta.url),
    new URL('../../catalogs/catalog.json', import.meta.url),
  ];
  for (const url of candidates) {
    try {
      const raw = await readFile(url, 'utf8');
      const parsed = JSON.parse(raw) as Catalog;
      cachedCatalog = parsed;
      return parsed;
    } catch {
      // continue to next candidate
    }
  }
  const fallback: Catalog = { primitives: [] };
  cachedCatalog = fallback;
  return fallback;
}

async function loadProtected(): Promise<string[]> {
  if (cachedProtected) return cachedProtected;
  try {
    const raw = await readFile(new URL('../../tf-l0-spec/spec/protected.json', import.meta.url), 'utf8');
    const parsed = JSON.parse(raw) as { protected_keywords?: string[] };
    cachedProtected = (parsed.protected_keywords || []).map(k => k.toLowerCase());
  } catch {
    cachedProtected = [];
  }
  return cachedProtected;
}

async function loadLaws(): Promise<Law[]> {
  if (cachedLaws) return cachedLaws;
  try {
    const raw = await readFile(new URL('../../tf-l0-spec/spec/laws.json', import.meta.url), 'utf8');
    const parsed = JSON.parse(raw) as { laws?: Law[] };
    cachedLaws = parsed.laws || [];
  } catch {
    cachedLaws = [];
  }
  return cachedLaws;
}

function extractSymbol(document: TextDocument, position: { line: number; character: number }): string | null {
  const text = document.getText();
  const offset = document.offsetAt(position);
  const isValid = (ch: string) => /[A-Za-z0-9_:@\/-]/.test(ch);
  let start = offset;
  while (start > 0 && isValid(text.charAt(start - 1))) {
    start -= 1;
  }
  let end = offset;
  while (end < text.length && isValid(text.charAt(end))) {
    end += 1;
  }
  if (start === end) return null;
  return text.slice(start, end);
}

function resolveCatalogEntry(catalog: Catalog, symbol: string): CatalogEntry | null {
  const primitives = catalog.primitives || [];
  const lowerSymbol = symbol.toLowerCase();
  const exact = primitives.find(entry => (entry.id || '').toLowerCase() === lowerSymbol);
  if (exact) return exact;

  const base = lowerSymbol.startsWith('tf:') ? lowerSymbol.split('@')[0] : null;
  if (base) {
    const withVersion = primitives.find(entry => (entry.id || '').toLowerCase().startsWith(`${base}@`));
    if (withVersion) return withVersion;
  }

  const nameMatch = primitives.find(entry => (entry.name || '').toLowerCase() === lowerSymbol);
  if (nameMatch) return nameMatch;

  const suffixMatch = primitives.find(entry => (entry.id || '').toLowerCase().includes(`/${lowerSymbol}@`));
  if (suffixMatch) return suffixMatch;

  return null;
}

function buildSignature(entry: CatalogEntry, fallback: string): string {
  const label = entry.domain && entry.name
    ? `${entry.domain}.${entry.name}`
    : entry.name || entry.id || fallback;
  const keys = Array.isArray(entry.keys) ? entry.keys : [];
  const params = keys.length ? keys.map(k => k?.name || 'arg').join(', ') : '...';
  return `${label}(${params})`;
}

function collectPrimRecords(ir: unknown, protectedKeywords: string[]): PrimRecord[] {
  const records: PrimRecord[] = [];
  const lowerProtected = protectedKeywords.map(k => k.toLowerCase());

  function visit(node: unknown, regionStack: string[]): void {
    if (!node || typeof node !== 'object') {
      return;
    }
    const anyNode = node as { [key: string]: unknown };
    if (anyNode.node === 'Region') {
      const kind = typeof anyNode.kind === 'string' ? anyNode.kind : '';
      const nextStack = kind ? regionStack.concat([kind]) : regionStack;
      const kids = Array.isArray(anyNode.children) ? anyNode.children : [];
      for (const child of kids) visit(child, nextStack);
      return;
    }
    if (anyNode.node === 'Prim') {
      const name = typeof anyNode.prim === 'string' ? anyNode.prim.toLowerCase() : '';
      if (name) {
        const protectedHit = lowerProtected.some(keyword => name.includes(keyword));
        const inAuthorize = regionStack.some(region => region.toLowerCase() === 'authorize');
        records.push({ name, offending: protectedHit && !inAuthorize });
      }
      return;
    }
    const kids = Array.isArray(anyNode.children) ? anyNode.children : [];
    for (const child of kids) visit(child, regionStack);
  }

  visit(ir, []);
  return records;
}

function createProtectedDiagnostics(records: PrimRecord[], document: TextDocument): Diagnostic[] {
  const diagnostics: Diagnostic[] = [];
  const text = document.getText();
  const lowered = text.toLowerCase();
  let offset = 0;
  for (const record of records) {
    if (!record.name) continue;
    const idx = lowered.indexOf(record.name, offset);
    if (idx === -1) {
      continue;
    }
    const end = idx + record.name.length;
    if (record.offending) {
      diagnostics.push({
        severity: DiagnosticSeverity.Error,
        message: `Protected op '${record.name}' must be inside Authorize{}`,
        source: 'tf-policy',
        range: {
          start: document.positionAt(idx),
          end: document.positionAt(end),
        },
      });
    }
    offset = end;
  }
  return diagnostics;
}
