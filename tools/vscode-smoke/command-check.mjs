#!/usr/bin/env node
import { runShowTraceSource } from '../../clients/vscode-tf/dist/extension.js';

const [fileArg, symbolArg] = process.argv.slice(2);
if (!fileArg || !symbolArg) {
  console.error('usage: node tools/vscode-smoke/command-check.mjs <file> <symbol>');
  process.exit(2);
}

const calls = [];
const requester = {
  async sendRequest(method, params) {
    calls.push({ method, params });
    return {
      start: { line: 0, character: 0 },
      end: { line: 0, character: symbolArg.length }
    };
  }
};

const document = {
  uri: { fsPath: fileArg },
  getText(range) {
    if (!range) {
      return `${symbolArg}`;
    }
    return symbolArg;
  }
};

const editor = {
  document,
  selection: {
    start: { line: 0, character: 0 },
    end: { line: 0, character: symbolArg.length }
  },
  revealRange() {}
};

const range = await runShowTraceSource({ requester, editor });

console.log(JSON.stringify({ calls, range }));
