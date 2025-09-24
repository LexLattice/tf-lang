"use strict";
var __createBinding = (this && this.__createBinding) || (Object.create ? (function(o, m, k, k2) {
    if (k2 === undefined) k2 = k;
    var desc = Object.getOwnPropertyDescriptor(m, k);
    if (!desc || ("get" in desc ? !m.__esModule : desc.writable || desc.configurable)) {
      desc = { enumerable: true, get: function() { return m[k]; } };
    }
    Object.defineProperty(o, k2, desc);
}) : (function(o, m, k, k2) {
    if (k2 === undefined) k2 = k;
    o[k2] = m[k];
}));
var __setModuleDefault = (this && this.__setModuleDefault) || (Object.create ? (function(o, v) {
    Object.defineProperty(o, "default", { enumerable: true, value: v });
}) : function(o, v) {
    o["default"] = v;
});
var __importStar = (this && this.__importStar) || (function () {
    var ownKeys = function(o) {
        ownKeys = Object.getOwnPropertyNames || function (o) {
            var ar = [];
            for (var k in o) if (Object.prototype.hasOwnProperty.call(o, k)) ar[ar.length] = k;
            return ar;
        };
        return ownKeys(o);
    };
    return function (mod) {
        if (mod && mod.__esModule) return mod;
        var result = {};
        if (mod != null) for (var k = ownKeys(mod), i = 0; i < k.length; i++) if (k[i] !== "default") __createBinding(result, mod, k[i]);
        __setModuleDefault(result, mod);
        return result;
    };
})();
Object.defineProperty(exports, "__esModule", { value: true });
exports.__setLanguageClient = __setLanguageClient;
exports.__setVscodeModule = __setVscodeModule;
exports.runShowTraceSource = runShowTraceSource;
exports.activate = activate;
exports.deactivate = deactivate;
let languageClient = null;
let vscodeModule = null;
function __setLanguageClient(client) {
    languageClient = client;
}
function __setVscodeModule(module) {
    vscodeModule = module;
}
function getVscode() {
    if (!vscodeModule) {
        const loaded = require('vscode');
        vscodeModule = loaded;
    }
    return vscodeModule;
}
async function ensureLanguageClient(context) {
    if (languageClient) {
        return languageClient;
    }
    try {
        const { LanguageClient, TransportKind } = await Promise.resolve().then(() => __importStar(require('vscode-languageclient/node')));
        const serverModule = context.asAbsolutePath('../../packages/tf-lsp-server/dist/server.js');
        const serverOptions = {
            run: { module: serverModule, transport: 2 /* TransportKind.ipc */ },
            debug: { module: serverModule, transport: 2 /* TransportKind.ipc */, options: { execArgv: ['--nolazy', '--inspect=6009'] } }
        };
        const clientOptions = { documentSelector: [{ scheme: 'file' }] };
        const client = new LanguageClient('tfLanguageServer', 'TF Language Server', serverOptions, clientOptions);
        context.subscriptions.push(client.start());
        languageClient = client;
        return client;
    }
    catch (error) {
        console.error('tf.showTraceSource: language client unavailable', error);
        return null;
    }
}
function activeEditor(editor) {
    if (editor) {
        return editor;
    }
    return getVscode().window.activeTextEditor ?? null;
}
function extractSymbol(editor) {
    const document = editor.document;
    const selection = editor.selection;
    if (selection && !selection.isEmpty) {
        const text = document.getText(selection).trim();
        if (text) {
            return text;
        }
    }
    const range = document.getWordRangeAtPosition(selection.active, /[A-Za-z0-9_:@\-]+/);
    if (!range) {
        return null;
    }
    const text = document.getText(range).trim();
    return text || null;
}
function toVscodeRange(vscodeApi, range) {
    const start = new vscodeApi.Position(range.start.line, range.start.character);
    const end = new vscodeApi.Position(range.end.line, range.end.character);
    return new vscodeApi.Range(start, end);
}
async function runShowTraceSource(client, editorOverride) {
    const vscodeApi = getVscode();
    const editor = activeEditor(editorOverride);
    if (!editor) {
        await vscodeApi.window.showWarningMessage('No active editor for TF trace source.');
        return;
    }
    const symbol = extractSymbol(editor);
    if (!symbol) {
        await vscodeApi.window.showWarningMessage('Select a symbol to locate its source.');
        return;
    }
    if (client.onReady) {
        await client.onReady();
    }
    const params = { symbol, file: editor.document.uri.fsPath };
    const result = await client.sendRequest('tf/sourceMap', params);
    if (!result) {
        await vscodeApi.window.showWarningMessage(`No source mapping found for ${symbol}.`);
        return;
    }
    const mappedRange = toVscodeRange(vscodeApi, result);
    editor.revealRange(mappedRange, 1 /* vscodeApi.TextEditorRevealType.InCenter */);
    editor.selection = new vscodeApi.Selection(mappedRange.start, mappedRange.end);
}
async function activate(context) {
    const vscodeApi = getVscode();
    await ensureLanguageClient(context);
    const disposable = vscodeApi.commands.registerCommand('tf.showTraceSource', async () => {
        if (!languageClient) {
            const ensured = await ensureLanguageClient(context);
            if (!ensured) {
                await vscodeApi.window.showWarningMessage('TF language client is not available.');
                return;
            }
        }
        await runShowTraceSource(languageClient);
    });
    context.subscriptions.push(disposable);
}
async function deactivate() {
    if (languageClient && languageClient.stop) {
        await languageClient.stop();
    }
    languageClient = null;
}
