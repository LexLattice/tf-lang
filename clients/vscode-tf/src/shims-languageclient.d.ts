declare module 'vscode-languageclient/node' {
  import type { Disposable } from 'vscode';

  export const enum TransportKind {
    ipc = 2
  }

  export interface ServerOptions {
    run: { module: string; transport: TransportKind };
    debug: { module: string; transport: TransportKind; options?: Record<string, unknown> };
  }

  export interface LanguageClientOptions {
    documentSelector?: Array<{ scheme?: string; language?: string }>;
  }

  export class LanguageClient {
    constructor(id: string, name: string, serverOptions: ServerOptions, clientOptions: LanguageClientOptions);
    start(): Disposable;
    onReady(): Promise<void>;
    sendRequest<R>(method: string, params: unknown): Promise<R>;
    stop(): Promise<void>;
  }
}
