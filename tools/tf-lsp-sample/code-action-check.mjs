import { readFile } from 'node:fs/promises';
import { resolve } from 'node:path';
import { pathToFileURL } from 'node:url';

import { LspClient } from './lsp-client.mjs';

function usage() {
  console.error('usage: node code-action-check.mjs --file <path>');
  process.exit(2);
}

function parseArgs(argv) {
  const args = { file: null };
  for (let i = 0; i < argv.length; i += 1) {
    const token = argv[i];
    if (token === '--file') {
      args.file = argv[i + 1] ?? null;
      i += 1;
      continue;
    }
  }
  if (!args.file) {
    usage();
  }
  return args;
}

async function main() {
  const args = parseArgs(process.argv.slice(2));
  const filePath = resolve(args.file);
  const text = await readFile(filePath, 'utf8');
  const uri = pathToFileURL(filePath).toString();

  const client = new LspClient();
  try {
    await client.initialize(null);
    await client.sendNotification('textDocument/didOpen', {
      textDocument: {
        uri,
        languageId: 'tf',
        version: 1,
        text,
      },
    });

    await new Promise((resolve) => {
      client.once('diagnostics', resolve);
    });

    const endPosition = { line: text.split(/\r?\n/).length - 1, character: (text.split(/\r?\n/).pop() ?? '').length };
    const actions = await client.sendRequest('textDocument/codeAction', {
      textDocument: { uri },
      range: { start: { line: 0, character: 0 }, end: endPosition },
      context: { diagnostics: [] },
    });

    const arrayActions = Array.isArray(actions) ? actions : [];
    console.log(`actions:${arrayActions.length}`);
    const inserted = arrayActions.some((action) => {
      const edits = action?.edit?.changes?.[uri] ?? [];
      return Array.isArray(edits) && edits.some((edit) => typeof edit?.newText === 'string' && edit.newText.includes('Authorize{ scope: "" }'));
    });
    if (inserted) {
      console.log('inserted:Authorize');
    }

    await client.sendNotification('textDocument/didClose', {
      textDocument: { uri },
    });
    await client.shutdown();
    process.exit(inserted ? 0 : 1);
  } catch (error) {
    console.error(error);
    try { await client.shutdown(); } catch {}
    process.exit(1);
  }
}

main();
