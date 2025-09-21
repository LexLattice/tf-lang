#!/usr/bin/env node
import { readdir, readFile, writeFile } from 'node:fs/promises';
import path from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';

function repoRoot() {
  const here = fileURLToPath(new URL('.', import.meta.url));
  return path.resolve(here, '..', '..');
}

async function loadTfCliUsage() {
  const cliPath = path.join(repoRoot(), 'packages', 'tf-compose', 'bin', 'tf.mjs');
  const src = await readFile(cliPath, 'utf8');
  const usageMatch = src.match(/Usage: tf <[^']+/);
  const usage = usageMatch ? usageMatch[0].replace('Usage: ', '') : 'tf <parse|check|canon|emit>';
  const commandMatch = src.match(/\[(?:'[^']+'(?:,\s*)?)+\]/);
  let commands = [];
  if (commandMatch) {
    commands = commandMatch[0]
      .replace(/[\[\]'\s]/g, '')
      .split(',')
      .filter(Boolean);
  }
  const primary = ['parse', 'check', 'canon', 'emit'];
  const listed = primary.filter(cmd => commands.includes(cmd));
  return { usage, commands: listed };
}

async function loadExamples() {
  const examplesDir = path.join(repoRoot(), 'examples', 'flows');
  const entries = await readdir(examplesDir, { withFileTypes: true });
  const selected = [];
  for (const entry of entries) {
    if (!entry.isFile() || !entry.name.endsWith('.tf')) continue;
    const fullPath = path.join(examplesDir, entry.name);
    const content = await readFile(fullPath, 'utf8');
    const trimmed = content.trimEnd();
    if (trimmed.length <= 160) {
      selected.push({ name: entry.name, content: trimmed });
    }
  }
  selected.sort((a, b) => a.name.localeCompare(b.name));
  return selected;
}

async function main() {
  const { usage, commands } = await loadTfCliUsage();
  const examples = await loadExamples();

  const lines = [];
  lines.push('# L0 DSL Cheatsheet (generated)');
  lines.push('');

  lines.push('## Basics');
  lines.push('- Chain primitives or regions with `|>` for sequential pipelines.');
  lines.push('- Use `seq{ ... }` blocks for multi-step sequences and `par{ ... }` for parallel branches.');
  lines.push('- Primitives are lowercase identifiers; pipeline nodes preserve the written order.');
  lines.push('');

  lines.push('## Args & Literals');
  lines.push('- Arguments appear as `prim(key=value, other=123)` with comma separators.');
  lines.push('- Strings accept single or double quotes with standard escape sequences.');
  lines.push('- Numbers allow optional `-` prefix and fractional parts; booleans use `true` or `false`, and `null` is accepted.');
  lines.push('- Arrays `[a, b, c]` and objects `{key: value}` are parsed recursively.');
  lines.push('');

  lines.push('## Regions');
  lines.push('- `authorize{ ... }` wraps a scoped block; optional `authorize(region="us"){ ... }` attributes sit in parentheses.');
  lines.push('- `txn{ ... }` creates a transactional region with the same attribute syntax.');
  lines.push('- Regions compose with pipelines just like primitives (`step |> authorize{ ... }`).');
  lines.push('');

  lines.push('## Comments');
  lines.push('- The parser does not recognize line or block comments; keep DSL files comment-free or encode notes via args.');
  lines.push('');

  lines.push('## CLI usage');
  lines.push(`- Commands mirror \`${usage}\` from \`packages/tf-compose/bin/tf.mjs\`.`);
  for (const cmd of commands) {
    if (cmd === 'parse') {
      lines.push('- `tf parse <flow.tf> [-o out.json]` emits canonical IR JSON.');
    } else if (cmd === 'check') {
      lines.push('- `tf check <flow.tf> [-o verdict.json]` validates effects and region constraints.');
    } else if (cmd === 'canon') {
      lines.push('- `tf canon <flow.tf> [-o canon.json]` normalizes flows with catalog laws.');
    } else if (cmd === 'emit') {
      lines.push('- `tf emit <flow.tf> [--lang ts|rs] [--out dir]` generates runnable adapters.');
    }
  }
  lines.push('');

  if (examples.length > 0) {
    lines.push('## Examples');
    for (const example of examples) {
      lines.push(`### ${example.name}`);
      lines.push('```tf');
      lines.push(example.content);
      lines.push('```');
      lines.push('');
    }
  }

  const outPath = path.join(repoRoot(), 'docs', 'l0-dsl.md');
  const payload = lines.join('\n');
  await writeFile(outPath, payload.endsWith('\n') ? payload : `${payload}\n`, 'utf8');
}

if (process.argv[1] && import.meta.url === pathToFileURL(path.resolve(process.argv[1])).href) {
  await main();
}

