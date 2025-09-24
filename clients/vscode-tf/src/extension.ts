import * as vscode from 'vscode';
import * as fs from 'node:fs';
import * as path from 'node:path';
import {
  LanguageClient,
  LanguageClientOptions,
  ServerOptions,
  TransportKind
} from 'vscode-languageclient/node';

let client: LanguageClient | undefined;

function resolveServerPath(context: vscode.ExtensionContext): string {
  const tryFile = (p: string | null) => (p && fs.existsSync(p)) ? p : '';

  // 1) bundled (future)
  const bundled = tryFile(context.asAbsolutePath('server.js'));
  if (bundled) return bundled;

  // 2) published package (future)
  try {
    // eslint-disable-next-line @typescript-eslint/no-var-requires
    const pkgPath = require.resolve('@tf-lang/tf-lsp-server/bin/server.mjs');
    const hit = tryFile(pkgPath);
    if (hit) return hit;
  } catch {
    /* ignore */
  }

  // 3) repo dev layout (current)
  const repo = path.join(context.extensionUri.fsPath, '..', '..', 'packages', 'tf-lsp-server', 'bin', 'server.mjs');
  const hit = tryFile(repo);
  if (hit) return hit;

  throw new Error('TF LSP server module not found (tried bundled, package, and repo paths).');
}

export async function activate(context: vscode.ExtensionContext): Promise<void> {
  if (!client) {
    const serverModule = resolveServerPath(context);
    const serverOptions: ServerOptions = {
      run:   { command: serverModule, transport: TransportKind.stdio },
      debug: { command: serverModule, transport: TransportKind.stdio }
    };
    const clientOptions: LanguageClientOptions = {
      documentSelector: [{ language: 'tf' }]
    };
    client = new LanguageClient('tfLanguageServer', 'TF Language Server', serverOptions, clientOptions);
    context.subscriptions.push(client.start());
  }

  // Command: tf.showTraceSource (send custom request to the running server)
  const disposable = vscode.commands.registerCommand('tf.showTraceSource', async () => {
    const editor = vscode.window.activeTextEditor;
    if (!editor) {
      void vscode.window.showInformationMessage('TF: No active editor.');
      return;
    }
    // Get fully qualified symbol under cursor, else selection
    const range =
      editor.document.getWordRangeAtPosition(editor.selection.active, /\btf:[a-z-]+\/[a-z-]+@\d+\b/i) ||
      (!editor.selection.isEmpty ? editor.selection : undefined);
    const symbol = range ? editor.document.getText(range).trim() : '';
    if (!symbol) {
      void vscode.window.showInformationMessage('TF: Place the cursor on a tf:<domain>/<name>@<major> symbol.');
      return;
    }
    const file = editor.document.uri.fsPath;

    try {
      // Ensure client is ready and send the custom request
      await client?.onReady();
      const rangeResp = await client?.sendRequest('tf/sourceMap', { symbol, file })
        .catch(() => null);

      if (!rangeResp) {
        void vscode.window.showInformationMessage('TF: No source range available for the selected symbol.');
        return;
      }
      const start = new vscode.Position(rangeResp.start.line, rangeResp.start.character);
      const end   = new vscode.Position(rangeResp.end.line,   rangeResp.end.character);
      editor.revealRange(new vscode.Range(start, end), vscode.TextEditorRevealType.InCenter);
    } catch (err) {
      const msg = err instanceof Error ? err.message : String(err);
      void vscode.window.showInformationMessage(`TF: Source map request failed: ${msg}`);
    }
  });
  context.subscriptions.push(disposable);
}

export async function deactivate(): Promise<void> {
  if (client) {
    try { await client.stop(); } catch { /* ignore */ }
    client = undefined;
  }
}
