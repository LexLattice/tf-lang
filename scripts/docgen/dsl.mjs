#!/usr/bin/env node
import { mkdir, readFile, readdir, writeFile } from 'node:fs/promises';
import path from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';

const __filename = fileURLToPath(import.meta.url);
const __dirname = path.dirname(__filename);

function resolveRepoRoot(root) {
  if (root) return root;
  return path.resolve(__dirname, '..', '..');
}

function detectFeatures(source) {
  return {
    hasPipeline: source.includes("makeToken('PIPE'"),
    hasSeqBlock: source.includes("'SEQ_OPEN'"),
    hasParBlock: source.includes("'PAR_OPEN'"),
    hasAuthorize: source.includes("'REGION_AUTH'"),
    hasTxn: source.includes("'REGION_TXN'"),
    hasStrings: source.includes("'STRING'"),
    hasNumbers: source.includes("'NUMBER'"),
    hasBooleans: source.includes("if (token.v === 'true')"),
    hasNull: source.includes("if (token.v === 'null')"),
    hasArrays: source.includes('function parseArray('),
    hasObjects: source.includes('function parseObject(')
  };
}

function buildBasicsSection(features) {
  const bullets = [];
  if (features.hasPipeline) {
    bullets.push('`step |> next` composes primitives left-to-right.');
  }
  if (features.hasSeqBlock) {
    bullets.push('`seq{ ... }` groups statements sequentially; semicolons separate explicit steps.');
  }
  if (features.hasParBlock) {
    bullets.push('`par{ ... }` evaluates children in parallel; wrap multiple steps with semicolons.');
  }
  if (bullets.length === 0) {
    bullets.push('Pipelines compose primitives and explicit `seq{}` / `par{}` blocks when available.');
  }
  bullets.push('Identifiers map to primitives and are normalized to lowercase during parsing.');
  return bullets;
}

function buildArgsSection(features) {
  const bullets = [];
  if (features.hasStrings) {
    bullets.push('Strings support single or double quotes with standard escape handling.');
  }
  if (features.hasNumbers) {
    bullets.push('Numbers accept integers and decimals with optional leading minus.');
  }
  if (features.hasBooleans) {
    bullets.push('Boolean literals `true` and `false` are parsed as actual booleans.');
  }
  if (features.hasNull) {
    bullets.push('`null` produces a JavaScript null literal.');
  }
  if (features.hasArrays) {
    bullets.push('Array literals use `[value, ...]` with trailing commas supported.');
  }
  if (features.hasObjects) {
    bullets.push('Object literals use `{ key: value, ... }` and accept string, identifier, or numeric keys.');
  }
  bullets.push('Argument lists appear as `prim(arg=value, ...)` and default to an empty object when omitted.');
  return bullets;
}

function buildRegionsSection(features) {
  const bullets = [];
  if (features.hasAuthorize) {
    bullets.push('`authorize{ ... }` wraps a region; optional `authorize(attrs){ ... }` attaches metadata.');
  }
  if (features.hasTxn) {
    bullets.push('`txn{ ... }` models transactional regions with optional attributes like `txn(scope="ledger"){ ... }`.');
  }
  if (bullets.length === 0) {
    bullets.push('Regions wrap blocks with optional `(key=value)` metadata when supported.');
  }
  return bullets;
}

function buildCommentsSection() {
  return [
    'The tokenizer does not implement comment skipping; treat `#`, `//`, or `/* */` as syntax errors and keep flows comment-free.'
  ];
}

async function loadCliCommands(cliSource) {
  const usageMatch = cliSource.match(/Usage: tf <([^>]+)>/);
  if (!usageMatch) {
    return [];
  }
  const commands = usageMatch[1]
    .split('|')
    .map(token => token.trim())
    .filter(Boolean);
  const primary = ['parse', 'check', 'canon', 'emit'];
  const descriptions = {
    parse: 'Parse a `.tf` file and emit canonical IR JSON.',
    check: 'Validate a flow against the catalog and region policies, returning JSON verdicts.',
    canon: 'Normalize a parsed flow using effect laws for deterministic ordering.',
    emit: 'Generate code for the requested language (TypeScript or Rust) under `out/`. Use `--lang ts|rs` and optionally `--out` for the destination.'
  };
  return primary
    .filter(cmd => commands.includes(cmd))
    .map(cmd => ({ cmd, description: descriptions[cmd] }));
}

async function loadShortExamples(root) {
  const flowsDir = path.join(root, 'examples', 'flows');
  const entries = await readdir(flowsDir);
  const selected = [];
  for (const entry of entries) {
    if (!entry.endsWith('.tf')) continue;
    const filePath = path.join(flowsDir, entry);
    const raw = await readFile(filePath, 'utf8');
    const trimmed = raw.trimEnd();
    const charCount = trimmed.length;
    const lineCount = trimmed === '' ? 0 : trimmed.split(/\r?\n/).length;
    if (charCount <= 80 && lineCount <= 6) {
      selected.push({ name: entry, content: trimmed });
    }
  }
  selected.sort((a, b) => a.name.localeCompare(b.name));
  return selected;
}

function renderSection(lines, title, bullets) {
  lines.push(`## ${title}`);
  lines.push('');
  for (const bullet of bullets) {
    lines.push(`- ${bullet}`);
  }
  lines.push('');
}

function renderCliTable(lines, commands) {
  lines.push('## CLI usage');
  lines.push('');
  if (!commands || commands.length === 0) {
    lines.push('No CLI commands detected in `packages/tf-compose/bin/tf.mjs`.');
    lines.push('');
    return;
  }
  lines.push('| Command | Summary |');
  lines.push('| --- | --- |');
  for (const { cmd, description } of commands) {
    lines.push(`| \`tf ${cmd}\` | ${description} |`);
  }
  lines.push('');
}

function renderExamples(lines, examples) {
  lines.push('## Examples');
  lines.push('');
  if (!examples || examples.length === 0) {
    lines.push('_No short examples (≤80 characters) were found in `examples/flows`.');
    lines.push('');
    return;
  }
  for (const example of examples) {
    lines.push(`### ${example.name}`);
    lines.push('');
    lines.push('```tf');
    lines.push(example.content);
    lines.push('```');
    lines.push('');
  }
}

export async function generateDSLDoc(options = {}) {
  const repoRoot = resolveRepoRoot(options.root);
  const parserPath = path.join(repoRoot, 'packages', 'tf-compose', 'src', 'parser.mjs');
  const cliPath = path.join(repoRoot, 'packages', 'tf-compose', 'bin', 'tf.mjs');
  const outPath = path.join(repoRoot, 'docs', 'l0-dsl.md');

  const [parserSource, cliSource, examples] = await Promise.all([
    readFile(parserPath, 'utf8'),
    readFile(cliPath, 'utf8'),
    loadShortExamples(repoRoot)
  ]);

  const features = detectFeatures(parserSource);
  const commands = await loadCliCommands(cliSource);

  const lines = [];
  lines.push('# L0 DSL Cheatsheet (generated)');
  lines.push('');

  renderSection(lines, 'Basics', buildBasicsSection(features));
  renderSection(lines, 'Args & Literals', buildArgsSection(features));
  renderSection(lines, 'Regions', buildRegionsSection(features));
  renderSection(lines, 'Comments', buildCommentsSection());
  renderCliTable(lines, commands);
  renderExamples(lines, examples);

  const output = lines.join('\n').replace(/\s+$/u, '').concat('\n');
  await mkdir(path.dirname(outPath), { recursive: true });
  await writeFile(outPath, output, 'utf8');
  return outPath;
}

if (process.argv[1] && import.meta.url === pathToFileURL(path.resolve(process.argv[1])).href) {
  await generateDSLDoc();
}
