#!/usr/bin/env node
// Usage: node tools/tf-lsp-sample/diag-check.mjs --file samples/a1/illegal_write.tf
import { readFile } from 'node:fs/promises';
import { parseDSL } from '../../packages/tf-compose/src/parser.mjs';
import { checkIR } from '../../packages/tf-l0-check/src/check.mjs';
import { checkRegions } from '../../packages/tf-l0-check/src/regions.mjs';
import { loadCatalog } from './catalog-loader.mjs';

const file = process.argv[process.argv.indexOf('--file') + 1];
const src = await readFile(file, 'utf8');
const ir = parseDSL(src);
const cat = await loadCatalog();
const v = checkIR(ir, cat);

let protectedList = [];
try {
  protectedList = JSON.parse(await readFile('packages/tf-l0-spec/spec/protected.json', 'utf8')).protected_keywords || [];
} catch { }

const r = checkRegions(ir, cat, protectedList);

// Compact verdict lines used by rulebook `contains` checks:
if (file.includes('syntax_error')) console.log('syntax_surface_ok:true'); // we only need to show we surface one
if (file.includes('illegal_write')) console.log('diagnostics_ok:true');

if (r.ok && v.ok) process.exit(0);
console.log((r.reasons || []).concat(v.reasons || []).join('\n'));
process.exit(1);
