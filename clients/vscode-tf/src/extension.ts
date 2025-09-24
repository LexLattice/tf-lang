import * as path from 'node:path';
import * as vscode from 'vscode';
import {
  LanguageClient,
  LanguageClientOptions,
  ServerOptions,
  TransportKind
} from 'vscode-languageclient/node';

let client: LanguageClient | undefined;

export async function activate(context: vscode.ExtensionContext): Promise<void> {
  if (client) {
    return;
  }

  const serverExecutable = context.asAbsolutePath(
    path.join('..', '..', 'packages', 'tf-lsp-server', 'bin', 'server.mjs')
  );

  const serverOptions: ServerOptions = {
    run: { command: serverExecutable, transport: TransportKind.stdio },
    debug: { command: serverExecutable, transport: TransportKind.stdio }
  };

  const clientOptions: LanguageClientOptions = {
    documentSelector: [{ language: 'tf' }],
    synchronize: {
      fileEvents: [
        vscode.workspace.createFileSystemWatcher('**/*.tf'),
        vscode.workspace.createFileSystemWatcher('**/*.tfvars')
      ]
    }
  };

  client = new LanguageClient(
    'tfLanguageServer',
    'TF Language Server',
    serverOptions,
    clientOptions
  );

  context.subscriptions.push(client);
  await client.start();
}

export async function deactivate(): Promise<void> {
  if (!client) {
    return;
  }

  await client.stop();
  client = undefined;
}
