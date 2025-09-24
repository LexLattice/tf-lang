import { createRequire } from 'node:module';
import { fileURLToPath } from 'node:url';
import path from 'node:path';
import fs from 'node:fs';
import { spawnSync } from 'node:child_process';

const require = createRequire(import.meta.url);
const Module = require('module');

const originalLoad = Module._load;
const stub = createStubEnvironment();
Module._load = function load(request, parent, isMain) {
  if (request === 'vscode') {
    return stub.vscodeApi;
  }
  return originalLoad.call(this, request, parent, isMain);
};

try {
  const baseDir = fileURLToPath(new URL('../../clients/vscode-tf/', import.meta.url));
  const extensionPath = path.resolve(baseDir, 'dist/extension.js');
  ensureBuilt(baseDir);
  const extension = await import(extensionPath);
  if (typeof extension.setSourceMapRequester !== 'function') {
    throw new Error('extension missing setSourceMapRequester export');
  }
  if (typeof extension.showTraceSource !== 'function') {
    throw new Error('extension missing showTraceSource export');
  }
  extension.setSourceMapRequester(async params => {
    stub.recordedParams.push(params);
    return stub.sampleRange;
  });
  extension.activate(stub.context);
  const command = stub.registeredCommands.get('tf.showTraceSource');
  if (!command) {
    throw new Error('tf.showTraceSource not registered');
  }
  const result = await command();
  if (!result) {
    throw new Error('showTraceSource command returned false');
  }
  if (!stub.reveals.length) {
    throw new Error('revealRange not triggered');
  }
  console.log(JSON.stringify({ ok: true, reveals: stub.reveals.length, params: stub.recordedParams }));
} finally {
  Module._load = originalLoad;
}

function ensureBuilt(baseDir) {
  const distPath = path.resolve(baseDir, 'dist/extension.js');
  if (fs.existsSync(distPath)) {
    return;
  }
  const tscPath = path.resolve(fileURLToPath(new URL('../../node_modules/typescript/bin/tsc', import.meta.url)));
  const configPath = path.resolve(baseDir, 'tsconfig.json');
  const result = spawnSync(process.execPath, [tscPath, '-p', configPath], { stdio: 'inherit' });
  if (result.status !== 0) {
    throw new Error('TypeScript build failed');
  }
}

function createStubEnvironment() {
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

  const text = 'trace tf:network/publish@1 example';
  const lineOffsets = computeLineOffsets(text);

  const document = {
    getText(range) {
      if (!range) return text;
      const start = offsetOfPosition(range.start);
      const end = offsetOfPosition(range.end);
      return text.slice(start, end);
    },
    offsetAt(position) {
      return offsetOfPosition(position);
    },
    uri: {
      toString() {
        return 'file:///tmp/sample.tf';
      },
      fsPath: '/tmp/sample.tf'
    }
  };

  function offsetOfPosition(position) {
    const base = lineOffsets[position.line] ?? 0;
    return base + position.character;
  }

  const active = new Position(0, text.indexOf('tf:network/publish@1'));
  const selection = new Selection(active, active);
  const reveals = [];
  const registeredCommands = new Map();
  const recordedParams = [];
  const sampleRange = {
    start: { line: 0, character: text.indexOf('tf:network') },
    end: { line: 0, character: text.indexOf('tf:network') + 'tf:network'.length }
  };

  const vscodeApi = {
    Position,
    Range,
    Selection,
    TextEditorRevealType: {
      Default: 0,
      InCenter: 1,
      InCenterIfOutsideViewport: 2,
      AtTop: 3
    },
    window: {
      get activeTextEditor() {
        return {
          document,
          selection,
          revealRange(range, how) {
            reveals.push({ range, how });
          }
        };
      }
    },
    commands: {
      registerCommand(command, callback) {
        registeredCommands.set(command, callback);
        return { dispose() {} };
      }
    }
  };

  const context = {
    subscriptions: []
  };

  function computeLineOffsets(source) {
    const offsets = [0];
    for (let i = 0; i < source.length; i++) {
      if (source[i] === '\n') {
        offsets.push(i + 1);
      }
    }
    return offsets;
  }

  return { vscodeApi, context, reveals, registeredCommands, recordedParams, sampleRange };
}
