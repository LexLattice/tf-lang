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
exports.activate = activate;
exports.deactivate = deactivate;
const path = __importStar(require("node:path"));
const vscode_1 = require("vscode");
const node_1 = require("vscode-languageclient/node");
let client;
function resolveServerModule(context) {
    return path.resolve(context.extensionPath, '..', '..', 'packages', 'tf-lsp-server', 'bin', 'server.mjs');
}
async function activate(context) {
    const serverModule = resolveServerModule(context);
    const serverOptions = {
        command: process.execPath,
        args: [serverModule],
        transport: node_1.TransportKind.stdio
    };
    const clientOptions = {
        documentSelector: [{ language: 'tf' }],
        synchronize: {
            fileEvents: vscode_1.workspace.createFileSystemWatcher('**/*.tf')
        },
        outputChannelName: 'TF Language Server',
        revealOutputChannelOn: node_1.RevealOutputChannelOn.Never,
        errorHandler: {
            error: () => ({ action: node_1.ErrorAction.Continue }),
            closed: () => ({ action: node_1.CloseAction.Restart })
        }
    };
    client = new node_1.LanguageClient('tf-language-server', 'TF Language Server', serverOptions, clientOptions);
    context.subscriptions.push(client);
    await client.start();
}
async function deactivate() {
    if (!client) {
        return;
    }
    await client.stop();
    client = undefined;
}
//# sourceMappingURL=extension.js.map