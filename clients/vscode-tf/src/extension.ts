import * as path from 'node:path';
import { workspace, ExtensionContext } from 'vscode';
import {
  CloseAction,
  ErrorAction,
  LanguageClient,
  LanguageClientOptions,
  RevealOutputChannelOn,
  ServerOptions,
  TransportKind
} from 'vscode-languageclient/node';

let client: LanguageClient | undefined;

function resolveServerModule(context: ExtensionContext): string {
  return path.resolve(
    context.extensionPath,
    '..',
    '..',
    'packages',
    'tf-lsp-server',
    'bin',
    'server.mjs'
  );
}

export async function activate(context: ExtensionContext): Promise<void> {
  const serverModule = resolveServerModule(context);

  const serverOptions: ServerOptions = {
    command: process.execPath,
    args: [serverModule],
    transport: TransportKind.stdio
  };

  const clientOptions: LanguageClientOptions = {
    documentSelector: [{ language: 'tf' }],
    synchronize: {
      fileEvents: workspace.createFileSystemWatcher('**/*.tf')
    },
    outputChannelName: 'TF Language Server',
    revealOutputChannelOn: RevealOutputChannelOn.Never,
    errorHandler: {
      error: () => ({ action: ErrorAction.Continue }),
      closed: () => ({ action: CloseAction.Restart })
    }
  };

  client = new LanguageClient(
    'tf-language-server',
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
