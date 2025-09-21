#!/usr/bin/env node
// scripts/audit/check-links.mjs
import { readdir, readFile, stat } from 'node:fs/promises';
import path from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';

const __dirname = path.dirname(fileURLToPath(import.meta.url));
const ROOT = path.resolve(__dirname, '../..');

async function collectMarkdownFiles() {
  const docsDir = path.join(ROOT, 'docs');
  const files = [];

  async function walk(dir) {
    const entries = await readdir(dir, { withFileTypes: true });
    for (const entry of entries) {
      const absPath = path.join(dir, entry.name);
      if (entry.isDirectory()) {
        await walk(absPath);
      } else if (entry.isFile() && entry.name.endsWith('.md')) {
        files.push(path.relative(ROOT, absPath).split(path.sep).join('/'));
      }
    }
  }

  try {
    await walk(docsDir);
  } catch (err) {
    if (!(err && err.code === 'ENOENT')) {
      throw err;
    }
  }

  files.sort();
  return files;
}

function extractLinks(markdown) {
  const links = [];
  const pattern = /!?(\[[^\]]*\])\(([^)]+)\)/g;
  for (const match of markdown.matchAll(pattern)) {
    const hrefWithMeta = match[2].trim();
    const spaceIndex = hrefWithMeta.indexOf(' ');
    const href = spaceIndex === -1 ? hrefWithMeta : hrefWithMeta.slice(0, spaceIndex);
    links.push(href);
  }
  return links;
}

function isRelativeLink(href) {
  if (!href) return false;
  if (href.startsWith('#')) return false;
  if (/^[a-zA-Z][a-zA-Z0-9+.-]*:/.test(href)) return false;
  return true;
}

async function existsRelative(baseFile, href) {
  const anchorIndex = href.indexOf('#');
  const target = anchorIndex === -1 ? href : href.slice(0, anchorIndex);
  if (!target) {
    return true;
  }
  let decoded = target;
  try {
    decoded = decodeURI(target);
  } catch (err) {
    decoded = target;
  }
  let resolved;
  if (decoded.startsWith('/')) {
    resolved = path.join(ROOT, decoded.replace(/^\/+/, ''));
  } else {
    const baseDir = path.dirname(path.join(ROOT, baseFile));
    resolved = path.resolve(baseDir, decoded);
  }
  try {
    await stat(resolved);
    return true;
  } catch (err) {
    return false;
  }
}

export async function run() {
  const markdownFiles = await collectMarkdownFiles();
  const targets = new Set(['README.md', ...markdownFiles]);

  const broken = [];
  const seen = new Set();

  for (const relPath of Array.from(targets).sort()) {
    const absPath = path.join(ROOT, relPath);
    let content;
    try {
      content = await readFile(absPath, 'utf8');
    } catch (err) {
      if (relPath === 'README.md') {
        throw err;
      }
      continue;
    }
    for (const href of extractLinks(content)) {
      if (!isRelativeLink(href)) continue;
      if (await existsRelative(relPath, href)) continue;
      const key = `${relPath}::${href}`;
      if (seen.has(key)) continue;
      seen.add(key);
      broken.push({ from: relPath, href });
    }
  }

  broken.sort((a, b) => {
    if (a.from === b.from) {
      return a.href.localeCompare(b.href);
    }
    return a.from.localeCompare(b.from);
  });

  const ok = broken.length === 0;
  return { ok, broken };
}

async function main() {
  const result = await run();
  process.stdout.write(`${JSON.stringify(result, null, 2)}\n`);
}

const isCli = process.argv[1]
  ? pathToFileURL(process.argv[1]).href === import.meta.url
  : false;

if (isCli) {
  main().catch((err) => {
    process.stderr.write(`audit:check-links failed: ${err?.stack || err}\n`);
    process.exitCode = 1;
  });
}
