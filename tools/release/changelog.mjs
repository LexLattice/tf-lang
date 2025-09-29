#!/usr/bin/env node
import { execFileSync } from 'node:child_process';
import { promises as fs } from 'node:fs';
import path from 'node:path';

import { emitJson, logStep, parseArgs, UsageError } from './_shared.mjs';

const ROOT = process.cwd();
const OUTPUT_PATH = path.join(ROOT, 'out/0.5/release/CHANGELOG.next.md');
const LIMIT = Number(process.env.CHANGELOG_LIMIT ?? '50');

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

function parseCommits({ limit, range }) {
  const args = ['log', '--no-merges', '--pretty=format:%H%x1f%s'];
  if (range) {
    args.push(range);
  }
  args.push('-n', String(limit));
  logStep(`git ${args.join(' ')}`);
  const raw = execFileSync('git', args, { encoding: 'utf8' });
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

async function writeChangelog(commits, outPath) {
  const grouped = groupCommits(commits);
  const sections = SECTION_ORDER.map((section) =>
    formatSection(section.title, grouped.get(section.type) ?? []),
  );
  const content = ['# CHANGELOG.next', '', ...sections].join('\n');

  await fs.mkdir(path.dirname(outPath), { recursive: true });
  await fs.writeFile(outPath, `${content}\n`, 'utf8');
}

async function main(argv) {
  const args = parseArgs(argv, {
    usage: 'node tools/release/changelog.mjs [options]',
    description: 'Generate the next release changelog stub from git history.',
    flags: {
      out: {
        description: 'Write the JSON status output to this path in addition to stdout.',
      },
      range: {
        description: 'Restrict git log to the provided range (e.g. v0.4.0..HEAD).',
      },
      dryRun: false,
      tag: false,
      verbose: {
        description: 'Emit progress information to stderr.',
      },
      quiet: {
        description: 'Suppress stdout emission of the JSON status.',
      },
    },
  });

  if (args.help) {
    process.stdout.write(args.helpText);
    return args;
  }

  if (args.verbose) {
    process.env.RELEASE_VERBOSE = '1';
  }

  const commits = parseCommits({ limit: LIMIT, range: args.range });
  await writeChangelog(commits, OUTPUT_PATH);
  const statusBody = await emitJson(
    { ok: true, file: path.relative(ROOT, OUTPUT_PATH) },
    args.out,
  );
  if (!args.quiet) {
    process.stdout.write(statusBody);
  }
  return args;
}

async function run() {
  let args;
  try {
    args = await main(process.argv.slice(2));
  } catch (error) {
    if (error instanceof UsageError) {
      if (error.message) {
        console.error(error.message);
      }
      if (error.helpText) {
        process.stderr.write(error.helpText);
      }
      process.exit(error.exitCode);
    }
    console.error(`changelog generation failed: ${error.message}`);
    if (args) {
      const failureBody = await emitJson(
        { ok: false, error: error.message },
        args.out,
      );
      if (!args.quiet) {
        process.stdout.write(failureBody);
      }
    }
    process.exit(1);
  }
}

run();
