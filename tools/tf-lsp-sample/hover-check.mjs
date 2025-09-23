import { resolve } from 'node:path';
import { pathToFileURL } from 'node:url';

import { LspClient } from './lsp-client.mjs';

function usage() {
  console.error('usage: node hover-check.mjs --symbol <symbol>');
  process.exit(2);
}

function parseArgs(argv) {
  const args = { symbol: null };
  for (let i = 0; i < argv.length; i += 1) {
    const token = argv[i];
    if (token === '--symbol') {
      args.symbol = argv[i + 1] ?? null;
      i += 1;
      continue;
    }
  }
  if (!args.symbol) {
    usage();
  }
  return args;
}

async function main() {
  const args = parseArgs(process.argv.slice(2));
  const client = new LspClient();
  const tempUri = pathToFileURL(resolve('out/tmp/hover.tf')).toString();
  try {
    await client.initialize(null);
    await client.sendNotification('textDocument/didOpen', {
      textDocument: {
        uri: tempUri,
        languageId: 'tf',
        version: 1,
        text: args.symbol,
      },
    });

    const hover = await client.sendRequest('textDocument/hover', {
      textDocument: { uri: tempUri },
      position: { line: 0, character: Math.max(args.symbol.length - 1, 0) },
    });

    await client.sendNotification('textDocument/didClose', {
      textDocument: { uri: tempUri },
    });

    const contents = hover?.contents;
    let value = '';
    if (!hover) {
      console.log('hover:null');
      await client.shutdown();
      process.exit(1);
    }
    if (typeof contents === 'string') {
      value = contents;
    } else if (Array.isArray(contents)) {
      value = contents.map((item) => (typeof item === 'string' ? item : item?.value ?? '')).join('\n');
    } else if (contents && typeof contents === 'object') {
      value = contents.value ?? '';
    }
    console.log(value);
    await client.shutdown();
    process.exit(value ? 0 : 1);
  } catch (error) {
    console.error(error);
    try { await client.shutdown(); } catch {}
    process.exit(1);
  }
}

main();
