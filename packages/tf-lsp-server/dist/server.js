import { createConnection, DiagnosticSeverity, MarkupKind, ProposedFeatures, TextDocumentSyncKind, TextDocuments } from 'vscode-languageserver/node';
import { TextDocument } from 'vscode-languageserver-textdocument';
import { promises as fs } from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
const connection = createConnection(ProposedFeatures.all);
const documents = new TextDocuments(TextDocument);
const parserModulePromise = import('../../tf-compose/src/parser.mjs');
const PROTECTED_NAMES = new Set(['sign-data', 'write-object']);
const moduleDir = path.dirname(fileURLToPath(import.meta.url));
const specDir = path.resolve(moduleDir, '../../tf-l0-spec/spec');
const catalogPath = path.join(specDir, 'catalog.json');
const lawsPath = path.join(specDir, 'laws.json');
const signaturesPath = path.join(specDir, 'signatures.demo.json');
const hoverDataPromise = loadHoverData();
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
connection.onInitialize((_params) => ({
    capabilities: {
        textDocumentSync: TextDocumentSyncKind.Incremental
    }
}));
documents.listen(connection);
connection.listen();
async function validateTextDocument(document) {
    const diagnostics = [];
    const text = document.getText();
    try {
        const { parseDSL } = await parserModulePromise;
        const ast = parseDSL(text);
        diagnostics.push(...collectProtectedDiagnostics(text, document, ast));
    }
    catch (error) {
        const diagnostic = createParseDiagnostic(error, document);
        if (diagnostic) {
            diagnostics.push(diagnostic);
        }
        else {
            connection.console.error(`parse failure: ${String(error)}`);
        }
    }
    connection.sendDiagnostics({ uri: document.uri, diagnostics });
}
function createParseDiagnostic(error, document) {
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
function clampPosition(position, document) {
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
function collectProtectedDiagnostics(text, document, ast) {
    const operations = collectOperations(ast, []);
    const diagnostics = [];
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
async function buildHoverPayload(document, position) {
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
function findPrimitiveAtOffset(text, offset) {
    const regex = /tf:[a-z0-9-]+\/[a-z0-9-]+@[0-9]+/gi;
    let match;
    while ((match = regex.exec(text)) !== null) {
        const start = match.index;
        const end = start + match[0].length;
        if (offset >= start && offset <= end) {
            return match[0].toLowerCase();
        }
    }
    return null;
}
async function loadHoverData() {
    const primitives = new Map();
    const laws = new Map();
    const signatures = new Map();
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
                    ? entry.effects.filter((value) => typeof value === 'string')
                    : [];
                primitives.set(id, { effects });
            }
        }
    }
    catch (error) {
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
    }
    catch (error) {
        connection.console.error(`hover laws load failed: ${String(error)}`);
    }
    try {
        const signaturesRaw = await fs.readFile(signaturesPath, 'utf8');
        const signaturesJson = JSON.parse(signaturesRaw);
        if (signaturesJson && typeof signaturesJson === 'object') {
            for (const [id, value] of Object.entries(signaturesJson)) {
                const normalized = normalizePrimitiveId(id);
                if (!normalized) {
                    continue;
                }
                signatures.set(normalized, value);
            }
        }
    }
    catch (error) {
        if (error?.code !== 'ENOENT') {
            connection.console.error(`hover signatures load failed: ${String(error)}`);
        }
    }
    return { primitives, laws, signatures };
}
function normalizePrimitiveId(value) {
    return typeof value === 'string' ? value.toLowerCase() : null;
}
function collectOperations(node, regionStack) {
    const results = [];
    visit(node, regionStack, results);
    return results;
}
function visit(node, regionStack, out) {
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
    const typedNode = node;
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
function escapeRegex(value) {
    return value.replace(/[.*+?^${}()|[\]\\]/g, '\\$&');
}
