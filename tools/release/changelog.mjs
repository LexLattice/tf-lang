#!/usr/bin/env node
import { execSync } from 'node:child_process';
import { promises as fs } from 'node:fs';
import path from 'node:path';

const ROOT = process.cwd();
const OUTPUT_PATH = path.join(ROOT, 'out/0.5/release/CHANGELOG.next.md');
const LIMIT = Number(process.env.CHANGELOG_LIMIT ?? '50');

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

function resolveSections() {
  const titleMap = new Map([
    ['feat', 'Features'],
    ['fix', 'Fixes'],
    ['chore', 'Chore'],
    ['docs', 'Docs'],
    ['ci', 'CI'],
    ['other', 'Other'],
  ]);
  const raw = process.env.CHANGELOG_TYPES ?? 'feat,fix,chore,docs,ci,other';
  const entries = raw
    .split(',')
    .map((item) => item.trim())
    .filter(Boolean);
  const seen = new Set();
  const normalized = [];
  for (const type of entries) {
    if (seen.has(type)) {
      continue;
    }
    seen.add(type);
    normalized.push({
      type,
      title:
        titleMap.get(type) ||
        type.replace(/(^|[-_\s])(\w)/g, (_, __, letter) => letter.toUpperCase()),
    });
  }
  if (!seen.has('other')) {
    normalized.push({ type: 'other', title: titleMap.get('other') });
  }
  return normalized;
}

const SECTION_ORDER = resolveSections();

function parseCommits(limit) {
  const raw = execSync(
    `git log --no-merges --pretty=format:%H%x1f%s -n ${limit}`,
    { encoding: 'utf8' },
  );
  const lines = raw.split('\n').filter(Boolean);
  return lines.map((line) => {
    const [hash, subject] = line.split('\u001f');
    return { hash, subject };
  });
}

function classify(subject) {
  const match = subject.match(/^(\w+)(?:\([^)]*\))?!?:\s*(.+)$/i);
  if (!match) {
    return { type: 'other', description: subject };
  }
  const [, rawType, desc] = match;
  const type = rawType.toLowerCase();
  const normalized = SECTION_ORDER.find((section) => section.type === type);
  if (!normalized) {
    return { type: 'other', description: subject };
  }
  return { type: normalized.type, description: desc.trim() || subject };
}

function groupCommits(commits) {
  const grouped = new Map();
  for (const section of SECTION_ORDER) {
    grouped.set(section.type, []);
  }
  for (const commit of commits) {
    const { type, description } = classify(commit.subject);
    const entry = {
      description,
      subject: commit.subject,
      hash: commit.hash,
    };
    grouped.get(type)?.push(entry);
  }
  return grouped;
}

function formatSection(title, entries) {
  const lines = [`## ${title}`];
  if (!entries.length) {
    lines.push('- _No changes._');
    return lines.join('\n');
  }
  for (const entry of entries) {
    const shortHash = entry.hash.slice(0, 7);
    lines.push(`- ${entry.description} (${shortHash})`);
  }
  return lines.join('\n');
}

async function main(options) {
  const commits = parseCommits(LIMIT);
  const grouped = groupCommits(commits);
  const sections = SECTION_ORDER.map((section) =>
    formatSection(section.title, grouped.get(section.type) ?? []),
  );
  const content = ['# CHANGELOG.next', '', ...sections].join('\n');

  await fs.mkdir(path.dirname(OUTPUT_PATH), { recursive: true });
  await fs.writeFile(OUTPUT_PATH, `${content}\n`, 'utf8');

  emit({ ok: true, file: path.relative(ROOT, OUTPUT_PATH) }, options);
}

const options = parseArgs(process.argv.slice(2));

main(options).catch((error) => {
  console.error(`changelog generation failed: ${error.message}`);
  emit({ ok: false, error: error.message }, options);
  process.exit(1);
});
