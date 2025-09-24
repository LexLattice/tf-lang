import type * as vscode from 'vscode';

type SourceMapRange = {
  start: { line: number; character: number };
  end: { line: number; character: number };
};

type SourceMapParams = {
  symbol: string;
  file: string;
};

interface SourceMapClient {
  onReady?: () => Promise<void>;
  sendRequest<R>(method: string, params: SourceMapParams): Promise<R>;
  stop?: () => Promise<void>;
}

let languageClient: SourceMapClient | null = null;
let vscodeModule: typeof import('vscode') | null = null;

export function __setLanguageClient(client: SourceMapClient | null): void {
  languageClient = client;
}

export function __setVscodeModule(module: typeof import('vscode') | null): void {
  vscodeModule = module;
}

function getVscode(): typeof import('vscode') {
  if (!vscodeModule) {
    const loaded = require('vscode');
    vscodeModule = loaded as typeof import('vscode');
  }
  return vscodeModule;
}

async function ensureLanguageClient(context: vscode.ExtensionContext): Promise<SourceMapClient | null> {
  if (languageClient) {
    return languageClient;
  }
  try {
    const { LanguageClient, TransportKind } = await import('vscode-languageclient/node');
    const serverModule = context.asAbsolutePath('../../packages/tf-lsp-server/dist/server.js');
    const serverOptions = {
      run: { module: serverModule, transport: TransportKind.ipc },
      debug: { module: serverModule, transport: TransportKind.ipc, options: { execArgv: ['--nolazy', '--inspect=6009'] } }
    };
    const clientOptions = { documentSelector: [{ scheme: 'file' }] };
    const client = new LanguageClient('tfLanguageServer', 'TF Language Server', serverOptions, clientOptions);
    context.subscriptions.push(client.start());
    languageClient = client;
    return client;
  } catch (error) {
    console.error('tf.showTraceSource: language client unavailable', error);
    return null;
  }
}

function activeEditor(editor?: vscode.TextEditor | null): vscode.TextEditor | null {
  if (editor) {
    return editor;
  }
  return getVscode().window.activeTextEditor ?? null;
}

function extractSymbol(editor: vscode.TextEditor): string | null {
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

function toVscodeRange(vscodeApi: typeof import('vscode'), range: SourceMapRange): vscode.Range {
  const start = new vscodeApi.Position(range.start.line, range.start.character);
  const end = new vscodeApi.Position(range.end.line, range.end.character);
  return new vscodeApi.Range(start, end);
}

export async function runShowTraceSource(
  client: SourceMapClient,
  editorOverride?: vscode.TextEditor | null
): Promise<void> {
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
  const params: SourceMapParams = { symbol, file: editor.document.uri.fsPath };
  const result = await client.sendRequest<SourceMapRange | null>('tf/sourceMap', params);
  if (!result) {
    await vscodeApi.window.showWarningMessage(`No source mapping found for ${symbol}.`);
    return;
  }
  const mappedRange = toVscodeRange(vscodeApi, result);
  editor.revealRange(mappedRange, vscodeApi.TextEditorRevealType.InCenter);
  editor.selection = new vscodeApi.Selection(mappedRange.start, mappedRange.end);
}

export async function activate(context: vscode.ExtensionContext): Promise<void> {
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
    await runShowTraceSource(languageClient as SourceMapClient);
  });
  context.subscriptions.push(disposable);
}

export async function deactivate(): Promise<void> {
  if (languageClient && languageClient.stop) {
    await languageClient.stop();
  }
  languageClient = null;
}
