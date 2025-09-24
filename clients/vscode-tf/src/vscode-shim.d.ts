declare module 'vscode' {
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

  export enum TextEditorRevealType {
    Default,
    InCenter,
    InCenterIfOutsideViewport,
    AtTop
  }

  export interface Disposable {
    dispose(): void;
  }

  export interface Uri {
    toString(): string;
    readonly fsPath: string;
  }

  export interface TextDocument {
    getText(range?: Range): string;
    offsetAt(position: Position): number;
    readonly uri: Uri;
  }

  export interface TextEditor {
    readonly document: TextDocument;
    readonly selection: Selection;
    revealRange(range: Range, revealType?: TextEditorRevealType): void;
  }

  export interface ExtensionContext {
    readonly subscriptions: Disposable[];
  }

  export const window: {
    readonly activeTextEditor: TextEditor | undefined;
  };

  export const commands: {
    registerCommand(command: string, callback: (...args: unknown[]) => unknown): Disposable;
  };
}
