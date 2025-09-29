#!/usr/bin/env node
import { promises as fs } from 'node:fs';
import path from 'node:path';

const ROOT = process.cwd();
const OUTPUT_PATH = path.join(ROOT, 'out/0.5/docs/index.json');

function parseArgs(argv) {
  const options = { json: false, quiet: false };
  for (const arg of argv) {
    if (arg === '--json') {
      options.json = true;
      continue;
    }
    if (arg === '--quiet') {
      options.quiet = true;
      continue;
    }
    console.error(`Unknown flag: ${arg}`);
    process.exit(1);
  }
  return options;
}

function emit(payload, { quiet, json }) {
  if (!quiet) {
    const output = JSON.stringify(payload);
    process.stdout.write(`${json ? output : output}\n`);
  }
}

async function main(options) {
  const generatedAt = new Date().toISOString();
  const artifact = {
    ok: true,
    generated_at: generatedAt,
    items: [],
  };

  await fs.mkdir(path.dirname(OUTPUT_PATH), { recursive: true });
  await fs.writeFile(OUTPUT_PATH, `${JSON.stringify(artifact, null, 2)}\n`, 'utf8');

  emit({ ok: true, output: path.relative(ROOT, OUTPUT_PATH) }, options);
}

const options = parseArgs(process.argv.slice(2));

main(options).catch((error) => {
  console.error(`docs build failed: ${error.message}`);
  emit({ ok: false, error: error.message }, options);
  process.exit(1);
});
