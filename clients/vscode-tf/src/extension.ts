import * as vscode from 'vscode';

export type SourceMapRequestParams = { symbol: string; file: string };
export type SourceMapRange = { start: { line: number; character: number }; end: { line: number; character: number } };
export type SourceMapRequester = (params: SourceMapRequestParams) => Promise<SourceMapRange | null>;

let requester: SourceMapRequester | null = null;

export function setSourceMapRequester(fn: SourceMapRequester | null): void {
  requester = fn;
}

export function activate(context: vscode.ExtensionContext): void {
  const disposable = vscode.commands.registerCommand('tf.showTraceSource', showTraceSource);
  context.subscriptions.push(disposable);
}

export function deactivate(): void {
  requester = null;
}

export async function showTraceSource(): Promise<boolean> {
  const editor = vscode.window.activeTextEditor;
  if (!editor) return false;
  const symbol = extractSymbol(editor);
  if (!symbol) return false;
  const sender = requester;
  if (!sender) return false;
  const range = await sender({ symbol, file: editor.document.uri.toString() });
  if (!range) return false;
  const vsRange = toVsRange(range);
  editor.revealRange(vsRange, vscode.TextEditorRevealType.InCenterIfOutsideViewport);
  return true;
}

function extractSymbol(editor: vscode.TextEditor): string | null {
  const { document, selection } = editor;
  const selected = selection.isEmpty ? '' : document.getText(selection).trim();
  if (selected) return selected;
  const text = document.getText();
  const offset = document.offsetAt(selection.active);
  let start = offset;
  while (start > 0 && isIdentifierChar(text[start - 1] || '')) start--;
  let end = offset;
  while (end < text.length && isIdentifierChar(text[end] || '')) end++;
  if (start === end) return null;
  return text.slice(start, end);
}

function toVsRange(range: SourceMapRange): vscode.Range {
  const start = new vscode.Position(range.start.line, range.start.character);
  const end = new vscode.Position(range.end.line, range.end.character);
  return new vscode.Range(start, end);
}

function isIdentifierChar(ch: string): boolean {
  return /[A-Za-z0-9_:\-@]/.test(ch);
}
