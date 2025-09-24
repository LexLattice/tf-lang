interface PositionLike {
  line: number;
  character: number;
}

interface RangeLike {
  start: PositionLike;
  end: PositionLike;
}

interface SelectionLike extends RangeLike {
  active?: PositionLike;
}

interface TextDocumentLike {
  getText(range?: RangeLike): string;
  uri?: { fsPath?: string };
  fileName?: string;
  offsetAt?(position: PositionLike): number;
  getWordRangeAtPosition?(position: PositionLike): RangeLike | undefined;
}

interface TextEditorLike {
  document: TextDocumentLike;
  selection: SelectionLike;
  revealRange?(range: RangeLike, revealType?: unknown): void;
}

type SourceMapRange = RangeLike;

export interface SourceMapRequestParams {
  symbol: string;
  file: string;
}

export interface SourceMapRequester {
  sendRequest<TResult>(method: string, params: SourceMapRequestParams): Promise<TResult>;
}

export interface ShowTraceSourceOptions {
  requester?: SourceMapRequester;
  editor?: TextEditorLike;
  symbol?: string;
  file?: string;
  reveal?(range: SourceMapRange): void | Promise<void>;
}

type VSCodeModule = {
  window?: { activeTextEditor?: TextEditorLike };
  commands?: { registerCommand(id: string, handler: () => unknown): { dispose(): void } };
  Selection?: new (start: PositionLike, end: PositionLike) => SelectionLike;
  TextEditorRevealType?: { InCenter?: unknown };
};

declare const require: { (name: string): unknown };

let vscodeModule: VSCodeModule | undefined;
try {
  vscodeModule = require('vscode') as VSCodeModule;
} catch {
  vscodeModule = undefined;
}

let activeRequester: SourceMapRequester | null = null;

export function registerSourceMapRequester(requester: SourceMapRequester | null): void {
  activeRequester = requester;
}

export async function runShowTraceSource(options: ShowTraceSourceOptions = {}): Promise<SourceMapRange | null> {
  const requester = options.requester ?? activeRequester;
  if (!requester) {
    return null;
  }

  const editor = options.editor ?? vscodeModule?.window?.activeTextEditor ?? null;
  if (!editor) {
    return null;
  }

  const symbol = options.symbol ?? extractSymbol(editor);
  if (!symbol) {
    return null;
  }

  const filePath = options.file ?? resolveFsPath(editor.document);
  if (!filePath) {
    return null;
  }

  let range: SourceMapRange | null;
  try {
    range = await requester.sendRequest<SourceMapRange | null>('tf/sourceMap', { symbol, file: filePath });
  } catch {
    return null;
  }

  if (!range) {
    return null;
  }

  if (options.reveal) {
    await options.reveal(range);
  } else if (vscodeModule && typeof editor.revealRange === 'function') {
    const revealType = vscodeModule.TextEditorRevealType?.InCenter;
    editor.revealRange(range, revealType);
    if (typeof vscodeModule.Selection === 'function') {
      editor.selection = new vscodeModule.Selection(range.start, range.end);
    } else {
      editor.selection = { start: range.start, end: range.end };
    }
  } else if (typeof editor.revealRange === 'function') {
    editor.revealRange(range);
  }

  return range;
}

export function activate(context: { subscriptions?: Array<{ dispose(): void }> }, options?: { requester?: SourceMapRequester }): void {
  if (options?.requester) {
    registerSourceMapRequester(options.requester);
  }

  if (!vscodeModule?.commands) {
    return;
  }

  const disposable = vscodeModule.commands.registerCommand('tf.showTraceSource', async () => {
    await runShowTraceSource();
  });

  if (context.subscriptions) {
    context.subscriptions.push(disposable);
  }
}

export function deactivate(): void {
  registerSourceMapRequester(null);
}

function extractSymbol(editor: TextEditorLike): string | null {
  const document = editor.document;
  const selection = editor.selection;
  if (!document || !selection) {
    return null;
  }

  const selected = safeGetText(document, selection).trim();
  if (selected) {
    return selected;
  }

  const active = selection.active ?? selection.start;
  if (!active) {
    return null;
  }

  if (typeof document.getWordRangeAtPosition === 'function') {
    const wordRange = document.getWordRangeAtPosition(active);
    if (wordRange) {
      const word = safeGetText(document, wordRange).trim();
      if (word) {
        return word;
      }
    }
  }

  const content = safeGetText(document);
  if (!content) {
    return null;
  }

  const offset = typeof document.offsetAt === 'function'
    ? document.offsetAt(active)
    : positionToOffset(content, active);

  return readWordAt(content, offset);
}

function safeGetText(document: TextDocumentLike, range?: RangeLike): string {
  try {
    return typeof document.getText === 'function' ? document.getText(range) : '';
  } catch {
    if (!range) {
      return '';
    }
    try {
      return document.getText();
    } catch {
      return '';
    }
  }
}

function resolveFsPath(document: TextDocumentLike): string | null {
  if (document.uri && typeof document.uri.fsPath === 'string') {
    return document.uri.fsPath;
  }
  if (typeof document.fileName === 'string') {
    return document.fileName;
  }
  return null;
}

function positionToOffset(text: string, position: PositionLike): number {
  if (position.line <= 0 && position.character <= 0) {
    return 0;
  }

  let line = 0;
  let character = 0;
  for (let index = 0; index < text.length; index += 1) {
    if (line === position.line && character === position.character) {
      return index;
    }
    const ch = text[index];
    if (ch === '\n') {
      line += 1;
      character = 0;
    } else if (ch === '\r') {
      if (text[index + 1] === '\n') {
        continue;
      }
      character += 1;
    } else {
      character += 1;
    }
  }

  return text.length;
}

function readWordAt(text: string, offset: number): string | null {
  if (!text) {
    return null;
  }

  const clampOffset = Math.max(0, Math.min(offset, text.length));
  const isIdentifier = (ch: string) => /[A-Za-z0-9_:@-]/.test(ch);

  let start = clampOffset;
  while (start > 0 && isIdentifier(text[start - 1] ?? '')) {
    start -= 1;
  }

  let end = clampOffset;
  while (end < text.length && isIdentifier(text[end] ?? '')) {
    end += 1;
  }

  if (start === end) {
    return null;
  }

  return text.slice(start, end);
}
