import type * as vscode from 'vscode';
type SourceMapParams = {
    symbol: string;
    file: string;
};
interface SourceMapClient {
    onReady?: () => Promise<void>;
    sendRequest<R>(method: string, params: SourceMapParams): Promise<R>;
    stop?: () => Promise<void>;
}
export declare function __setLanguageClient(client: SourceMapClient | null): void;
export declare function __setVscodeModule(module: typeof import('vscode') | null): void;
export declare function runShowTraceSource(client: SourceMapClient, editorOverride?: vscode.TextEditor | null): Promise<void>;
export declare function activate(context: vscode.ExtensionContext): Promise<void>;
export declare function deactivate(): Promise<void>;
export {};
