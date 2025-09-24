declare module 'vscode' {
  export type Thenable<T> = PromiseLike<T>;

  export interface Disposable {
    dispose(): void;
  }

  export interface ExtensionContext {
    readonly subscriptions: Disposable[];
    asAbsolutePath(relativePath: string): string;
  }

  export namespace commands {
    function registerCommand(command: string, callback: (...args: unknown[]) => unknown): Disposable;
    function executeCommand<T = unknown>(command: string, ...args: unknown[]): Thenable<T | undefined>;
  }

  export namespace window {
    const activeTextEditor: TextEditor | undefined;
    function showWarningMessage(message: string): Thenable<void>;
  }

  export const enum TextEditorRevealType {
    InCenter = 1
  }

  export class Position {
    constructor(line: number, character: number);
    readonly line: number;
    readonly character: number;
  }

  export class Range {
    constructor(start: Position, end: Position);
    readonly start: Position;
    readonly end: Position;
  }

  export class Selection extends Range {
    constructor(anchor: Position, active: Position);
    readonly anchor: Position;
    readonly active: Position;
    readonly isEmpty: boolean;
  }

  export interface Uri {
    readonly fsPath: string;
  }

  export interface TextDocument {
    readonly uri: Uri;
    getText(range?: Range): string;
    getWordRangeAtPosition(position: Position, regexp?: RegExp): Range | undefined;
  }

  export interface TextEditor {
    document: TextDocument;
    selection: Selection;
    selections: Selection[];
    revealRange(range: Range, revealType?: TextEditorRevealType): void;
  }
}
