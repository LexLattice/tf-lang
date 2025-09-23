#!/usr/bin/env node
// Stub that calls your server's "wrap with Authorize" code action directly (module import)
// Replace the import below to match your server implementation once it exists.
import { wrapWithAuthorize } from '../../packages/tf-lsp-server/src/actions/wrap-authorize.mjs';
import { readFile } from 'node:fs/promises';
const file = process.argv[process.argv.indexOf('--file') + 1];
const src = await readFile(file, 'utf8');
const edit = wrapWithAuthorize(src, { rangeHint: null });
if (!edit) process.exit(1);
console.log('inserted:Authorize'); // rulebook checks for this token
process.exit(0);
