import * as path from 'node:path';
import { existsSync } from 'node:fs';
import * as vscode from 'vscode';
import {
  LanguageClient,
  LanguageClientOptions,
  ServerOptions,
  TransportKind
} from 'vscode-languageclient/node';

let client: LanguageClient | undefined;

function resolveServerModule(context: vscode.ExtensionContext): string {
  const repoRoot = path.join(context.extensionPath, '..', '..');
  const devServer = path.join(repoRoot, 'packages', 'tf-lsp-server', 'bin', 'server.mjs');
  if (existsSync(devServer)) {
    return devServer;
  }
  const packagedServer = path.join(context.extensionPath, 'packages', 'tf-lsp-server', 'bin', 'server.mjs');
  if (existsSync(packagedServer)) {
    return packagedServer;
  }
  throw new Error('TF language server executable not found.');
}

export async function activate(context: vscode.ExtensionContext): Promise<void> {
  const serverModule = resolveServerModule(context);
  const serverOptions: ServerOptions = {
    run: {
      command: process.execPath,
      args: [serverModule],
      options: {
        cwd: path.dirname(serverModule),
        env: {
          ...process.env,
          NODE_NO_WARNINGS: '1'
        }
      }
    },
    debug: {
      command: process.execPath,
      args: [serverModule, '--inspect=6009'],
      options: {
        cwd: path.dirname(serverModule)
      }
    },
    transport: TransportKind.stdio
  };

  const clientOptions: LanguageClientOptions = {
    documentSelector: [
      { scheme: 'file', language: 'tf' },
      { scheme: 'untitled', language: 'tf' }
    ],
    synchronize: {
      configurationSection: 'tf'
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
  if (client) {
    await client.stop();
  }
}
