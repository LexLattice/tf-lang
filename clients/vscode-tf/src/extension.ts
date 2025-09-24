import { existsSync } from 'node:fs';
import { createRequire } from 'node:module';
import path from 'node:path';
import { spawn, type ChildProcessWithoutNullStreams } from 'node:child_process';
import {
  StreamMessageReader,
  StreamMessageWriter,
  createMessageConnection,
  type MessageConnection,
  RequestType
} from 'vscode-jsonrpc/node.js';

type VsModule = typeof import('vscode');

interface DisposableLike { dispose(): unknown; }

interface ExtensionLikeContext {
  asAbsolutePath(relativePath: string): string;
  subscriptions: DisposableLike[];
}

interface BasicPosition { line: number; character: number; }

interface BasicRange { start: BasicPosition; end: BasicPosition; }

interface EditorLike {
  selection: BasicRange & { isEmpty: boolean; active: BasicPosition };
  document: {
    getText(range?: BasicRange): string;
    getWordRangeAtPosition(position: BasicPosition, regex?: RegExp): BasicRange | undefined;
    uri: { fsPath: string };
  };
  revealRange(range: unknown, revealType?: unknown): void;
}

export interface SourceMapParams {
  symbol: string;
  file: string;
  src_range?: SourceMapRange | null;
}

export interface SourceMapRange {
  start: { line: number; character: number };
  end: { line: number; character: number };
}

export interface SourceMapWorkflowInput {
  symbol: string | null;
  file: string | null;
}

export type SourceMapRequester = (params: SourceMapParams) => Promise<SourceMapRange | null>;
export type SourceMapRevealer = (range: SourceMapRange) => void;
export type SourceMapNotifier = (message: string) => void;

const SourceMapRequest = new RequestType<SourceMapParams, SourceMapRange | null, void>('tf/sourceMap');

let vscodeModule: Promise<VsModule> | null = null;
let lspConnection: MessageConnection | null = null;
let lspProcess: ChildProcessWithoutNullStreams | null = null;
let connectionPromise: Promise<MessageConnection> | null = null;
let initializePromise: Promise<void> | null = null;

async function loadVscode(): Promise<VsModule> {
  if (!vscodeModule) {
    vscodeModule = import('vscode');
  }
  return vscodeModule;
}

const requireForResolution = createRequire(import.meta.url);

function escapeRe(value: string): string {
  return value.replace(/[|\\{}()[\]^$+*?.-]/g, '\\$&');
}

function buildLiteralRegExp(symbol: string): RegExp | null {
  try {
    return new RegExp(escapeRe(symbol), 'gm');
  } catch {
    return null;
  }
}

function resolveServerModule(context: ExtensionLikeContext): string {
  const bundled = context.asAbsolutePath('server.js');
  if (bundled && existsSync(bundled)) {
    return bundled;
  }
  try {
    return requireForResolution.resolve('@tf-lang/tf-lsp-server/bin/server.mjs');
  } catch {
    // fall through to repo-relative resolution
  }
  const repoRelative = context.asAbsolutePath(
    path.join('..', '..', 'packages', 'tf-lsp-server', 'dist', 'server.js')
  );
  if (existsSync(repoRelative)) {
    return repoRelative;
  }
  throw new Error('Unable to locate TF language server module');
}

async function ensureConnection(context: ExtensionLikeContext): Promise<MessageConnection> {
  if (!connectionPromise) {
    connectionPromise = (async () => {
      try {
        const serverModule = resolveServerModule(context);
        lspProcess = spawn(process.execPath, [serverModule, '--stdio'], { stdio: ['pipe', 'pipe', 'pipe'] });
        const reader = new StreamMessageReader(lspProcess.stdout);
        const writer = new StreamMessageWriter(lspProcess.stdin);
        const connection = createMessageConnection(reader, writer);
        connection.listen();
        lspConnection = connection;
        lspProcess.stderr.setEncoding('utf8');
        lspProcess.stderr.on('data', data => {
          const text = data.toString();
          if (text.trim()) {
            console.error(`[tf-lsp] ${text.trim()}`);
          }
        });
        lspProcess.on('exit', () => {
          connection.dispose();
          lspConnection = null;
          lspProcess = null;
          connectionPromise = null;
          initializePromise = null;
        });
        lspProcess.on('error', () => {
          connection.dispose();
          lspConnection = null;
          lspProcess = null;
          connectionPromise = null;
          initializePromise = null;
        });
        return connection;
      } catch (err) {
        connectionPromise = null;
        lspProcess = null;
        lspConnection = null;
        throw err;
      }
    })();
  }
  return connectionPromise;
}

async function ensureInitialized(context: ExtensionLikeContext): Promise<MessageConnection> {
  const connection = await ensureConnection(context);
  if (!initializePromise) {
    initializePromise = (async () => {
      await connection.sendRequest('initialize', {
        processId: process.pid,
        capabilities: {},
        rootUri: null,
        workspaceFolders: null
      });
      connection.sendNotification('initialized', {});
    })();
  }
  await initializePromise;
  return connection;
}

function pickSymbol(editor: EditorLike): string | null {
  const document = editor.document;
  const selection = editor.selection;
  const tokenRange = document.getWordRangeAtPosition(selection.active, /[A-Za-z0-9_:@\-]+/);
  if (tokenRange) {
    const token = document.getText(tokenRange).trim();
    if (token) {
      return token;
    }
  }
  if (!selection.isEmpty) {
    const selected = document.getText(selection).trim();
    if (selected) {
      return selected;
    }
  }
  return null;
}

export async function runSourceMapWorkflow(
  input: SourceMapWorkflowInput,
  request: SourceMapRequester,
  reveal: SourceMapRevealer,
  notify?: SourceMapNotifier
): Promise<SourceMapRange | null> {
  const symbol = (input.symbol || '').trim();
  const file = input.file ? input.file.trim() : '';
  if (!symbol || !file) {
    notify?.('Select a symbol to map.');
    return null;
  }
  const re = buildLiteralRegExp(symbol);
  if (!re) {
    notify?.('The selected symbol is not a valid search pattern.');
    return null;
  }
  const range = await request({ symbol, file });
  if (!range) {
    notify?.('No source range available for the selected symbol.');
    return null;
  }
  reveal(range);
  return range;
}

export async function activate(context: ExtensionLikeContext): Promise<void> {
  const vscode = await loadVscode();
  const command = vscode.commands.registerCommand('tf.showTraceSource', async () => {
    const editor = vscode.window.activeTextEditor as EditorLike | undefined;
    if (!editor) {
      notifyUser(vscode, 'No active editor for TF source map.');
      return;
    }
    const symbol = pickSymbol(editor);
    if (!symbol) {
      notifyUser(vscode, 'Place the cursor on a symbol to map.');
      return;
    }
    const file = editor.document.uri.fsPath;
    try {
      await runSourceMapWorkflow(
        { symbol, file },
        async params => {
          const connection = await ensureInitialized(context);
          return connection.sendRequest(SourceMapRequest, params);
        },
        range => {
          const start = new vscode.Position(range.start.line, range.start.character);
          const end = new vscode.Position(range.end.line, range.end.character);
          const target = new vscode.Range(start, end);
          editor.revealRange(target, vscode.TextEditorRevealType.InCenter);
        },
        message => notifyUser(vscode, message)
      );
    } catch (err) {
      notifyUser(vscode, `Failed to request source map: ${err instanceof Error ? err.message : String(err)}`);
    }
  });
  context.subscriptions.push(command as DisposableLike);
}

function notifyUser(vscode: VsModule, message: string): void {
  void vscode.window.showInformationMessage(message);
}

export async function deactivate(): Promise<void> {
  if (lspConnection) {
    try {
      await lspConnection.sendRequest('shutdown');
    } catch {
      // ignore shutdown errors
    }
    lspConnection.dispose();
    lspConnection = null;
  }
  if (lspProcess) {
    lspProcess.stdin.end();
    lspProcess.kill();
    lspProcess = null;
  }
  connectionPromise = null;
  initializePromise = null;
  vscodeModule = null;
}
