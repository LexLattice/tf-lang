#!/usr/bin/env node
// Usage: node tools/tf-lsp-sample/hover-check.mjs --symbol "tf:network/publish@1"
import { readFile } from 'node:fs/promises';
const sym = process.argv[process.argv.indexOf('--symbol') + 1];
const cat = JSON.parse(await readFile('packages/tf-l0-spec/spec/catalog.json', 'utf8'));
const entry = (cat.primitives || []).find(p => p.id === sym);
if (!entry) process.exit(1);
console.log(`effects:${JSON.stringify(entry.effects || [])}`);
process.exit(0);
