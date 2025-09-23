import { readFile } from 'node:fs/promises';
import { pathToFileURL } from 'node:url';
import { resolve } from 'node:path';

import { LspClient } from './lsp-client.mjs';

function usage() {
  console.error('usage: node diag-check.mjs --file <path>');
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
  const documentUri = pathToFileURL(filePath).toString();

  const client = new LspClient();
  try {
    await client.initialize(null);
    const diagnosticsPromise = new Promise((resolve) => {
      client.once('diagnostics', (payload) => {
        resolve(payload?.diagnostics ?? []);
      });
    });

    await client.sendNotification('textDocument/didOpen', {
      textDocument: {
        uri: documentUri,
        languageId: 'tf',
        version: 1,
        text,
      },
    });

    const diagnostics = await diagnosticsPromise;

    const arrayDiagnostics = Array.isArray(diagnostics) ? diagnostics : [];
    const hasProtectedViolation = arrayDiagnostics.some((diag) =>
      typeof diag?.message === 'string' && diag.message.includes("Protected op")
    );
    const hasParseError = arrayDiagnostics.some((diag) =>
      typeof diag?.message === 'string' && diag.message.startsWith('Parse error')
    );

    console.log(`diagnostics_ok:${arrayDiagnostics.length > 0}`);
    console.log(`syntax_surface_ok:${hasParseError}`);
    if (hasProtectedViolation) {
      for (const diag of arrayDiagnostics) {
        if (typeof diag?.message === 'string') {
          console.log(diag.message);
        }
      }
    }

    await client.shutdown();

    process.exit(hasProtectedViolation ? 1 : 0);
  } catch (error) {
    console.error(error);
    try { await client.shutdown(); } catch {}
    process.exit(1);
  }
}

main();
