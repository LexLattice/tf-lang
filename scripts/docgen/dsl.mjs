#!/usr/bin/env node
import { readFile, writeFile, readdir } from 'node:fs/promises';
import path from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';

const __dirname = path.dirname(fileURLToPath(import.meta.url));
const repoRoot = path.resolve(__dirname, '..', '..');
const PARSER_PATH = path.join(repoRoot, 'packages', 'tf-compose', 'src', 'parser.mjs');
const CLI_PATH = path.join(repoRoot, 'packages', 'tf-compose', 'bin', 'tf.mjs');
const EXAMPLES_DIR = path.join(repoRoot, 'examples', 'flows');
const OUTPUT_PATH = path.join(repoRoot, 'docs', 'l0-dsl.md');

const MAX_EXAMPLE_LINES = 6;
const MAX_EXAMPLE_CHARS = 240;
const MAX_EXAMPLES = 12;

async function loadUsageLine() {
  const cliSource = await readFile(CLI_PATH, 'utf8');
  const match = cliSource.match(/Usage: tf [^']+/);
  if (match) {
    return match[0].trim();
  }
  return 'Usage: tf <parse|check|canon|emit> <flow.tf> [--out path]';
}

async function loadParserFacts() {
  const source = await readFile(PARSER_PATH, 'utf8');
  return {
    supportsAuthorize: source.includes("REGION_AUTH"),
    supportsTxn: source.includes("REGION_TXN"),
    supportsSeqBlocks: source.includes("SEQ_OPEN"),
    supportsParBlocks: source.includes("PAR_OPEN")
  };
}

function describeLiterals() {
  return [
    'Strings accept single or double quotes with standard escape handling.',
    'Numbers support optional leading `-` and fractional parts.',
    'Boolean and null literals map to `true`, `false`, and `null`.',
    'Arrays allow trailing commas and can nest arbitrary literal forms.',
    'Objects accept string, identifier, or numeric keys with trailing commas.'
  ];
}

function describeBasics(parserFacts) {
  const lines = [];
  if (parserFacts.supportsSeqBlocks) {
    lines.push('`a |> b` composes primitives into a left-associated sequence.');
    lines.push('`seq{ ... }` groups steps explicitly; semicolons separate statements inside the block.');
  } else {
    lines.push('Sequence composition uses the `|>` operator.');
  }
  if (parserFacts.supportsParBlocks) {
    lines.push('`par{ ... }` evaluates children in parallel; separate branches with semicolons.');
  }
  lines.push('Bare identifiers call primitives; add `(key=value, ...)` to supply arguments.');
  return lines;
}

function describeRegions(parserFacts) {
  const lines = [];
  if (parserFacts.supportsAuthorize) {
    lines.push('`authorize{ ... }` fences steps that require explicit capabilities.');
    lines.push('Add attributes with `authorize(scope="kms.sign"){ ... }`; attributes are parsed as key/value pairs.');
  }
  if (parserFacts.supportsTxn) {
    lines.push('`txn{ ... }` introduces a transactional region with the same attribute syntax.');
  }
  lines.push('Region blocks behave like sequence blocks for canonicalization boundaries.');
  return lines;
}

function describeComments() {
  return ['The current tokenizer does not recognize `#` or `//` comments; keep `.tf` files comment-free.'];
}

async function loadExamples() {
  const entries = await readdir(EXAMPLES_DIR, { withFileTypes: true });
  const snippets = [];
  for (const entry of entries) {
    if (!entry.isFile() || !entry.name.endsWith('.tf')) {
      continue;
    }
    const examplePath = path.join(EXAMPLES_DIR, entry.name);
    const contents = await readFile(examplePath, 'utf8');
    const trimmed = contents.trimEnd();
    const lineCount = trimmed.split(/\r?\n/).length;
    if (lineCount > MAX_EXAMPLE_LINES) {
      continue;
    }
    if (trimmed.length > MAX_EXAMPLE_CHARS) {
      continue;
    }
    snippets.push({ name: entry.name, contents: trimmed });
  }
  snippets.sort((a, b) => a.name.localeCompare(b.name));
  return snippets.slice(0, MAX_EXAMPLES);
}

function buildSection(title, bullets) {
  const lines = [`## ${title}`];
  for (const bullet of bullets) {
    lines.push(`* ${bullet}`);
  }
  return lines;
}

async function buildDslMarkdown() {
  const usageLine = await loadUsageLine();
  const parserFacts = await loadParserFacts();
  const lines = ['# L0 DSL Cheatsheet (generated)'];

  lines.push('');
  lines.push(...buildSection('Basics', describeBasics(parserFacts)));
  lines.push('');
  lines.push(...buildSection('Args & Literals', describeLiterals()));
  lines.push('');
  lines.push(...buildSection('Regions', describeRegions(parserFacts)));
  lines.push('');
  lines.push(...buildSection('Comments', describeComments()));
  lines.push('');
  const cliBullets = [
    `${usageLine}.`,
    '`tf parse` → emit canonical IR JSON for a flow.',
    '`tf check` → validate effects and region fences using the current catalog.',
    '`tf canon` → apply registered algebraic laws for normalization.',
    '`tf emit --lang ts|rs` → generate runnable scaffolding in the requested language.'
  ];
  lines.push(...buildSection('CLI usage', cliBullets));

  const examples = await loadExamples();
  if (examples.length > 0) {
    lines.push('');
    lines.push('## Examples');
    for (const example of examples) {
      lines.push('');
      lines.push(`### ${example.name}`);
      lines.push('```tf');
      lines.push(example.contents);
      lines.push('```');
    }
  }

  let doc = lines.join('\n');
  if (!doc.endsWith('\n')) {
    doc += '\n';
  }
  return doc;
}

export async function generateDslDoc({ outputPath = OUTPUT_PATH } = {}) {
  const markdown = await buildDslMarkdown();
  await writeFile(outputPath, markdown, 'utf8');
  return markdown;
}

async function main() {
  await generateDslDoc();
}

if (process.argv[1] && import.meta.url === pathToFileURL(path.resolve(process.argv[1])).href) {
  await main();
}
