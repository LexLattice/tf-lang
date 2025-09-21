#!/usr/bin/env node
import { mkdir, readdir, readFile, writeFile } from 'node:fs/promises';
import path from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';

const __dirname = path.dirname(fileURLToPath(import.meta.url));
const ROOT = path.resolve(__dirname, '../..');
const OUT_PATH = path.join(ROOT, 'docs/l0-dsl.md');
const EXAMPLES_DIR = path.join(ROOT, 'examples/flows');
const ALWAYS_INCLUDE = new Set(['run_publish.tf', 'signing.tf']);

function ensureTrailingNewline(payload) {
  return payload.endsWith('\n') ? payload : `${payload}\n`;
}

function formatSection(title, bodyLines) {
  return [`## ${title}`, '', ...bodyLines, ''];
}

function trimExample(content) {
  return content.replace(/\s+$/s, '').replace(/^\s+/s, match => match.includes('\n') ? '' : match);
}

function pickExamples(entries) {
  const filtered = entries.filter(entry => {
    if (ALWAYS_INCLUDE.has(entry.name)) return true;
    return entry.lines <= 4 && entry.content.length <= 200;
  });
  const missing = [...ALWAYS_INCLUDE].filter(name => !filtered.some(entry => entry.name === name));
  for (const name of missing) {
    const fallback = entries.find(entry => entry.name === name);
    if (fallback) {
      filtered.push(fallback);
    }
  }
  return filtered
    .sort((a, b) => a.name.localeCompare(b.name))
    .map(entry => ({ name: entry.name, content: trimExample(entry.raw) }));
}

async function loadExamples() {
  const files = await readdir(EXAMPLES_DIR);
  const tfFiles = files.filter(f => f.endsWith('.tf'));
  const entries = [];
  for (const name of tfFiles) {
    const raw = await readFile(path.join(EXAMPLES_DIR, name), 'utf8');
    const trimmed = raw.trim();
    const lines = trimmed.length === 0 ? 0 : trimmed.split(/\r?\n/).length;
    entries.push({ name, raw, content: trimmed, lines });
  }
  return pickExamples(entries);
}

async function buildDoc() {
  const examples = await loadExamples();

  const lines = ['# L0 DSL Cheatsheet (generated)', ''];

  lines.push(...formatSection('Basics', [
    'The DSL composes primitives with the pipeline operator `|>`. A single line such as ``serialize |> hash`` creates a sequential flow.',
    'Use `seq{ ... }` blocks to spell out multi-line sequences. Steps inside a block are separated with semicolons (`;`).',
    '`par{ ... }` introduces parallel branches. Each branch is parsed like a standalone flow and must be terminated with a semicolon unless it is the final branch.'
  ]));

  lines.push(...formatSection('Args & Literals', [
    'Arguments follow the form `prim(key=value, ...)`. Strings accept both single and double quotes and support standard escape sequences.',
    'Numbers accept optional leading minus signs and fractional components. Bare identifiers map to lower-cased primitive IDs or literal booleans (`true`, `false`) and `null`.',
    'Arrays (`[a, b, c]`) and objects (`{ key: value }`) are supported recursively, so complex payloads can be passed directly in-line.'
  ]));

  lines.push(...formatSection('Regions', [
    '`authorize{ ... }` wraps a sub-flow that requires policy checks. Optional attributes may appear as `authorize(scope="admin"){ ... }` before the block.',
    '`txn{ ... }` declares a transaction region. It shares the same attribute syntax as `authorize{}` and evaluates its children sequentially.'
  ]));

  lines.push(...formatSection('Comments', [
    'The grammar does not include line or block comments yet. Keep flows self-documenting or maintain commentary alongside the `.tf` files.'
  ]));

  lines.push(...formatSection('CLI usage', [
    'The `tf` helper under `packages/tf-compose/bin/tf.mjs` exposes the main workflows:',
    '- `tf parse <flow.tf>` → parse and emit the canonical IR JSON.',
    '- `tf check <flow.tf>` → run the lattice-aware checker and print the verdict JSON.',
    '- `tf canon <flow.tf>` → normalize the IR using catalog + law data.',
    '- `tf emit --lang ts|rs <flow.tf>` → write language-specific scaffolding into `out/0.4/codegen-*`.'
  ]));

  if (examples.length > 0) {
    lines.push('## Examples');
    lines.push('');
    for (const example of examples) {
      lines.push(`### ${example.name}`);
      lines.push('');
      lines.push('```tf');
      lines.push(example.content);
      lines.push('```');
      lines.push('');
    }
  }

  const payload = ensureTrailingNewline(lines.join('\n'));
  await mkdir(path.dirname(OUT_PATH), { recursive: true });
  await writeFile(OUT_PATH, payload, 'utf8');
}

if (process.argv[1] && import.meta.url === pathToFileURL(path.resolve(process.argv[1])).href) {
  await buildDoc();
}

export { buildDoc };
