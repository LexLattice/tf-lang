import { createConnection, ProposedFeatures, TextDocuments, TextDocumentSyncKind, DiagnosticSeverity } from "vscode-languageserver/node";
import { TextDocument } from "vscode-languageserver-textdocument";
import { readFile } from "node:fs/promises";
import path from "node:path";
import { fileURLToPath, pathToFileURL } from "node:url";
const connection = createConnection(ProposedFeatures.all);
const documents = new TextDocuments(TextDocument);
const currentFile = fileURLToPath(import.meta.url);
const currentDir = path.dirname(currentFile);
const parserUrl = pathToFileURL(path.resolve(currentDir, "../..", "tf-compose", "src", "parser.mjs")).href;
const protectedPath = path.resolve(currentDir, "../..", "tf-l0-spec", "spec", "protected.json");
const catalogPath = path.resolve(currentDir, "../..", "tf-l0-spec", "spec", "catalog.json");
const lawsPath = path.resolve(currentDir, "../..", "tf-l0-spec", "spec", "laws.json");
const signaturesPath = path.resolve(currentDir, "../..", "tf-l0-spec", "spec", "signatures.demo.json");
let parsePromise;
let protectedKeywordsPromise;
let catalogPromise;
let lawPromise;
let signaturePromise;
connection.onInitialize((_params) => ({
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
connection.onHover(async (params) => {
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
async function validateTextDocument(document) {
    const diagnostics = [];
    const text = document.getText();
    let root;
    try {
        const parseDSL = await loadParser();
        root = parseDSL(text);
    }
    catch (error) {
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
async function loadParser() {
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
async function loadProtectedKeywords() {
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
async function loadCatalog() {
    if (!catalogPromise) {
        catalogPromise = readFile(catalogPath, "utf8")
            .then((contents) => extractCatalogMap(safeJsonParse(contents)))
            .catch(() => new Map());
    }
    return catalogPromise;
}
async function loadLaws() {
    if (!lawPromise) {
        lawPromise = readFile(lawsPath, "utf8")
            .then((contents) => extractLawMap(safeJsonParse(contents)))
            .catch(() => new Map());
    }
    return lawPromise;
}
async function loadSignatures() {
    if (!signaturePromise) {
        signaturePromise = readFile(signaturesPath, "utf8")
            .then((contents) => extractSignatureMap(safeJsonParse(contents)))
            .catch(() => new Map());
    }
    return signaturePromise;
}
function safeJsonParse(text) {
    try {
        return JSON.parse(text);
    }
    catch {
        return undefined;
    }
}
function extractProtectedList(value) {
    if (typeof value !== "object" || value === null) {
        return [];
    }
    const maybeKeywords = value.protected_keywords;
    if (!Array.isArray(maybeKeywords)) {
        return [];
    }
    return maybeKeywords.filter((item) => typeof item === "string");
}
function extractCatalogMap(value) {
    const map = new Map();
    if (typeof value !== "object" || value === null) {
        return map;
    }
    const primitives = value.primitives;
    if (!Array.isArray(primitives)) {
        return map;
    }
    for (const entry of primitives) {
        if (typeof entry !== "object" || entry === null) {
            continue;
        }
        const id = entry.id;
        if (typeof id !== "string") {
            continue;
        }
        const effectsValue = entry.effects;
        const effects = Array.isArray(effectsValue)
            ? effectsValue.filter((effect) => typeof effect === "string")
            : [];
        map.set(id, { id, effects });
    }
    return map;
}
function extractLawMap(value) {
    const map = new Map();
    if (typeof value !== "object" || value === null) {
        return map;
    }
    const laws = value.laws;
    if (!Array.isArray(laws)) {
        return map;
    }
    for (const entry of laws) {
        if (typeof entry !== "object" || entry === null) {
            continue;
        }
        const lawId = entry.id;
        const applies = entry.applies_to;
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
function extractSignatureMap(value) {
    const map = new Map();
    if (typeof value !== "object" || value === null) {
        return map;
    }
    const entries = Object.entries(value);
    for (const [key, signature] of entries) {
        if (typeof key === "string") {
            map.set(key, signature);
        }
    }
    return map;
}
function collectProtectedViolations(root, protectedKeywords) {
    if (!root) {
        return [];
    }
    const results = [];
    const lowerKeywords = protectedKeywords.map((item) => item.toLowerCase());
    const visit = (node, authorizeDepth) => {
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
function buildRangeMap(tokens, text, document) {
    const map = new Map();
    const uniqueTokens = Array.from(new Set(tokens));
    for (const token of uniqueTokens) {
        map.set(token, findTokenRanges(token, text, document));
    }
    return map;
}
function findTokenRanges(token, text, document) {
    if (token.length === 0) {
        return [];
    }
    const ranges = [];
    const pattern = new RegExp(escapeForRegExp(token), "g");
    let match;
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
function takeRange(token, map) {
    const ranges = map.get(token);
    if (!ranges || ranges.length === 0) {
        return undefined;
    }
    return ranges.shift();
}
function escapeForRegExp(value) {
    return value.replace(/[.*+?^${}()|[\]\\]/g, "\\$&");
}
function createParseDiagnostic(error, document) {
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
function extractMessage(error) {
    if (typeof error === "string") {
        return error;
    }
    if (error && typeof error === "object" && "message" in error) {
        const maybeMessage = error.message;
        if (typeof maybeMessage === "string") {
            return maybeMessage;
        }
    }
    return undefined;
}
function isParseModule(value) {
    if (typeof value !== "object" || value === null) {
        return false;
    }
    const maybeFunction = value.parseDSL;
    return typeof maybeFunction === "function";
}
function findPrimitiveIdentifier(text, offset) {
    const pattern = /tf:[A-Za-z0-9_-]+\/[A-Za-z0-9_-]+@[0-9]+/g;
    let match;
    while ((match = pattern.exec(text)) !== null) {
        const start = match.index;
        const end = start + match[0].length;
        if (offset >= start && offset <= end) {
            return match[0];
        }
    }
    return undefined;
}
function formatSignature(value) {
    if (value === undefined) {
        return "(signature unavailable)";
    }
    try {
        return JSON.stringify(value, null, 2);
    }
    catch {
        return "(signature unavailable)";
    }
}
