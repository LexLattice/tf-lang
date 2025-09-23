declare module "vscode-languageserver/node" {
  export interface InitializeParams {}
  export interface InitializeResult {
    capabilities: { textDocumentSync: number };
  }
  export interface Position {
    line: number;
    character: number;
  }
  export interface Range {
    start: Position;
    end: Position;
  }
  export interface Diagnostic {
    range: Range;
    severity?: number;
    source?: string;
    message: string;
  }
  export interface Hover {
    contents: { kind: string; value: string };
  }
  export interface HoverParams {
    textDocument: { uri: string };
    position: Position;
  }
  export const DiagnosticSeverity: {
    Error: number;
    Warning: number;
    Information: number;
    Hint: number;
  };
  export const ProposedFeatures: { all: unknown };
  export const TextDocumentSyncKind: {
    None: number;
    Full: number;
    Incremental: number;
  };
  export interface Connection {
    onInitialize(handler: (params: InitializeParams) => InitializeResult): void;
    onHover(handler: (params: HoverParams) => Hover | undefined | Promise<Hover | undefined>): void;
    sendDiagnostics(payload: { uri: string; diagnostics: Diagnostic[] }): void;
    listen(): void;
  }
  export function createConnection(features: unknown): Connection;
  export class TextDocuments<T> {
    constructor(documentCtor: { new (...args: unknown[]): T });
    readonly syncKind: number;
    listen(connection: Connection): void;
    onDidOpen(listener: (event: { document: T }) => void): void;
    onDidChangeContent(listener: (event: { document: T }) => void): void;
    onDidClose(listener: (event: { document: T }) => void): void;
    get(uri: string): T | undefined;
  }
}

declare module "vscode-languageserver-textdocument" {
  export class TextDocument {
    readonly uri: string;
    getText(): string;
    positionAt(offset: number): { line: number; character: number };
    offsetAt(position: { line: number; character: number }): number;
  }
}
