import { strict as assert } from 'node:assert';
import path from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';

const __filename = fileURLToPath(import.meta.url);
const __dirname = path.dirname(__filename);

const extensionUrl = pathToFileURL(path.join(__dirname, '../../clients/vscode-tf/dist/extension.js')).href;
const extension = await import(extensionUrl);

class Position {
  constructor(line, character) {
    this.line = line;
    this.character = character;
  }
}

class Range {
  constructor(start, end) {
    this.start = start;
    this.end = end;
  }
}

class Selection extends Range {
  constructor(anchor, active) {
    super(anchor, active);
    this.anchor = anchor;
    this.active = active;
    this.isEmpty = anchor.line === active.line && anchor.character === active.character;
  }
}

const mockVscode = {
  Position,
  Range,
  Selection,
  TextEditorRevealType: { InCenter: 1 },
  window: {
    activeTextEditor: null,
    async showWarningMessage() {
      mockVscode.__warnings.push(Array.from(arguments));
    }
  },
  commands: {
    registerCommand() {
      return { dispose() {} };
    }
  },
  __warnings: []
};

extension.__setVscodeModule(mockVscode);

class FakeDocument {
  constructor(text) {
    this.uri = { fsPath: '/tmp/fake.tf' };
    this._text = text;
  }

  getText() {
    return this._text;
  }

  getWordRangeAtPosition() {
    return undefined;
  }
}

class FakeEditor {
  constructor(text) {
    this.document = new FakeDocument(text);
    this._selection = new Selection(new Position(0, 0), new Position(0, text.length));
    this.selections = [this._selection];
    this.revealed = null;
  }

  get selection() {
    return this._selection;
  }

  set selection(value) {
    this._selection = value;
    this.selections[0] = value;
  }

  revealRange(range, revealType) {
    this.revealed = { range, revealType };
  }
}

const calls = [];
const stubClient = {
  async onReady() {
    calls.push(['onReady']);
  },
  async sendRequest(method, params) {
    calls.push([method, params]);
    return { start: { line: 1, character: 2 }, end: { line: 1, character: 8 } };
  }
};

const editor = new FakeEditor('tf:network/publish@1');
await extension.runShowTraceSource(stubClient, editor);

assert.deepEqual(calls[0], ['onReady']);
assert.equal(calls[1][0], 'tf/sourceMap');
assert.equal(calls[1][1].symbol, 'tf:network/publish@1');
assert.equal(calls[1][1].file, '/tmp/fake.tf');
assert.ok(editor.revealed, 'editor did not reveal range');
assert.equal(editor.revealed.range.start.line, 1);
assert.equal(editor.selection.start.character, 2);

console.log(JSON.stringify({ ok: true, calls: calls.length }));
