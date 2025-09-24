"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
exports.registerSourceMapRequester = registerSourceMapRequester;
exports.runShowTraceSource = runShowTraceSource;
exports.activate = activate;
exports.deactivate = deactivate;
let vscodeModule;
try {
    vscodeModule = require('vscode');
}
catch {
    vscodeModule = undefined;
}
let activeRequester = null;
function registerSourceMapRequester(requester) {
    activeRequester = requester;
}
async function runShowTraceSource(options = {}) {
    const requester = options.requester ?? activeRequester;
    if (!requester) {
        return null;
    }
    const editor = options.editor ?? vscodeModule?.window?.activeTextEditor ?? null;
    if (!editor) {
        return null;
    }
    const symbol = options.symbol ?? extractSymbol(editor);
    if (!symbol) {
        return null;
    }
    const filePath = options.file ?? resolveFsPath(editor.document);
    if (!filePath) {
        return null;
    }
    let range;
    try {
        range = await requester.sendRequest('tf/sourceMap', { symbol, file: filePath });
    }
    catch {
        return null;
    }
    if (!range) {
        return null;
    }
    if (options.reveal) {
        await options.reveal(range);
    }
    else if (vscodeModule && typeof editor.revealRange === 'function') {
        const revealType = vscodeModule.TextEditorRevealType?.InCenter;
        editor.revealRange(range, revealType);
        if (typeof vscodeModule.Selection === 'function') {
            editor.selection = new vscodeModule.Selection(range.start, range.end);
        }
        else {
            editor.selection = { start: range.start, end: range.end };
        }
    }
    else if (typeof editor.revealRange === 'function') {
        editor.revealRange(range);
    }
    return range;
}
function activate(context, options) {
    if (options?.requester) {
        registerSourceMapRequester(options.requester);
    }
    if (!vscodeModule?.commands) {
        return;
    }
    const disposable = vscodeModule.commands.registerCommand('tf.showTraceSource', async () => {
        await runShowTraceSource();
    });
    if (context.subscriptions) {
        context.subscriptions.push(disposable);
    }
}
function deactivate() {
    registerSourceMapRequester(null);
}
function extractSymbol(editor) {
    const document = editor.document;
    const selection = editor.selection;
    if (!document || !selection) {
        return null;
    }
    const selected = safeGetText(document, selection).trim();
    if (selected) {
        return selected;
    }
    const active = selection.active ?? selection.start;
    if (!active) {
        return null;
    }
    if (typeof document.getWordRangeAtPosition === 'function') {
        const wordRange = document.getWordRangeAtPosition(active);
        if (wordRange) {
            const word = safeGetText(document, wordRange).trim();
            if (word) {
                return word;
            }
        }
    }
    const content = safeGetText(document);
    if (!content) {
        return null;
    }
    const offset = typeof document.offsetAt === 'function'
        ? document.offsetAt(active)
        : positionToOffset(content, active);
    return readWordAt(content, offset);
}
function safeGetText(document, range) {
    try {
        return typeof document.getText === 'function' ? document.getText(range) : '';
    }
    catch {
        if (!range) {
            return '';
        }
        try {
            return document.getText();
        }
        catch {
            return '';
        }
    }
}
function resolveFsPath(document) {
    if (document.uri && typeof document.uri.fsPath === 'string') {
        return document.uri.fsPath;
    }
    if (typeof document.fileName === 'string') {
        return document.fileName;
    }
    return null;
}
function positionToOffset(text, position) {
    if (position.line <= 0 && position.character <= 0) {
        return 0;
    }
    let line = 0;
    let character = 0;
    for (let index = 0; index < text.length; index += 1) {
        if (line === position.line && character === position.character) {
            return index;
        }
        const ch = text[index];
        if (ch === '\n') {
            line += 1;
            character = 0;
        }
        else if (ch === '\r') {
            if (text[index + 1] === '\n') {
                continue;
            }
            character += 1;
        }
        else {
            character += 1;
        }
    }
    return text.length;
}
function readWordAt(text, offset) {
    if (!text) {
        return null;
    }
    const clampOffset = Math.max(0, Math.min(offset, text.length));
    const isIdentifier = (ch) => /[A-Za-z0-9_:@-]/.test(ch);
    let start = clampOffset;
    while (start > 0 && isIdentifier(text[start - 1] ?? '')) {
        start -= 1;
    }
    let end = clampOffset;
    while (end < text.length && isIdentifier(text[end] ?? '')) {
        end += 1;
    }
    if (start === end) {
        return null;
    }
    return text.slice(start, end);
}
