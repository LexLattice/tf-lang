import { readdir, readFile } from 'node:fs/promises';
import path from 'node:path';
import { fileURLToPath } from 'node:url';

import { writeJsonCanonical } from './utils.mjs';

const ROOT = path.resolve(fileURLToPath(new URL('../../', import.meta.url)));
const OUT_DIR = path.join(ROOT, 'out', '0.4', 'tests');
const IGNORE_DIRS = new Set(['.git', 'node_modules', 'out', 'dist', 'build', '.pnpm', 'target']);
const TEST_EXTENSIONS = new Set(['.mjs', '.js', '.ts']);

const missingHeaders = [];
const missingSidecars = [];
const extraMeta = [];

const metaBases = new Set();
const rsBases = new Set();

function toPosix(p) {
  return p.split(path.sep).join('/');
}

async function walk(dir) {
  const entries = await readdir(dir, { withFileTypes: true });
  entries.sort((a, b) => a.name.localeCompare(b.name));
  for (const entry of entries) {
    if (entry.isSymbolicLink()) continue;
    if (entry.isDirectory()) {
      if (IGNORE_DIRS.has(entry.name)) continue;
      await walk(path.join(dir, entry.name));
    } else if (entry.isFile()) {
      await handleFile(path.join(dir, entry.name));
    }
  }
}

function extractLeadingComment(contents, file) {
  let index = 0;
  if (contents.startsWith('#!')) {
    const newlineIndex = contents.indexOf('\n');
    if (newlineIndex === -1) {
      return null;
    }
    index = newlineIndex + 1;
  }
  while (index < contents.length) {
    const char = contents[index];
    if (/\s/u.test(char)) {
      index += 1;
      continue;
    }
    if (char === '/' && contents[index + 1] === '/') {
      const lines = [];
      while (index < contents.length && contents[index] === '/' && contents[index + 1] === '/') {
        let lineStart = index + 2;
        let lineEnd = lineStart;
        while (lineEnd < contents.length && contents[lineEnd] !== '\n' && contents[lineEnd] !== '\r') {
          lineEnd += 1;
        }
        lines.push(contents.slice(lineStart, lineEnd));
        index = lineEnd;
        if (contents[index] === '\r') index += 1;
        if (contents[index] === '\n') index += 1;
      }
      return { type: 'line', text: lines.join('\n') };
    }
    if (char === '/' && contents[index + 1] === '*') {
      const endIndex = contents.indexOf('*/', index + 2);
      if (endIndex === -1) {
        throw new Error(`Unterminated block comment in ${file}`);
      }
      const inside = contents.slice(index + 2, endIndex);
      return { type: 'block', text: inside };
    }
    break;
  }
  return null;
}

function hasTfTestHeader(contents, file) {
  const comment = extractLeadingComment(contents, file);
  if (!comment) {
    return false;
  }
  let text = comment.text;
  if (comment.type === 'block') {
    text = text
      .split(/\r?\n/)
      .map((line) => line.replace(/^\s*\*/u, '').trim())
      .join('\n');
  }
  return text.includes('@tf-test');
}

async function handleFile(absPath) {
  const rel = toPosix(path.relative(ROOT, absPath));
  if (rel.endsWith('.meta')) {
    metaBases.add(rel.slice(0, -'.meta'.length));
    return;
  }

  const ext = path.extname(rel);
  if (rel.includes('/tests/') && ext === '.rs') {
    rsBases.add(rel.slice(0, -ext.length));
    return;
  }

  if (!TEST_EXTENSIONS.has(ext)) return;
  if (!rel.includes('.test.')) return;

  const contents = await readFile(absPath, 'utf8');
  if (!hasTfTestHeader(contents, rel)) {
    missingHeaders.push(rel);
  }
}

async function main() {
  await walk(ROOT);

  for (const base of rsBases) {
    if (!metaBases.has(base)) {
      missingSidecars.push({ test: `${base}.rs`, expected: `${base}.meta` });
    }
  }

  for (const base of metaBases) {
    if (!rsBases.has(base)) {
      extraMeta.push(`${base}.meta`);
    }
  }

  missingHeaders.sort((a, b) => a.localeCompare(b));
  missingSidecars.sort((a, b) => a.test.localeCompare(b.test));
  extraMeta.sort((a, b) => a.localeCompare(b));

  const report = {
    ok: missingHeaders.length === 0 && missingSidecars.length === 0 && extraMeta.length === 0,
    missingHeaders,
    missingSidecars,
    extraMeta,
  };

  const target = path.join(OUT_DIR, 'metadata-report.json');
  console.log(JSON.stringify(report));
  await writeJsonCanonical(target, report);

  if (!report.ok) {
    console.warn('Metadata audit found issues.');
    process.exitCode = 1;
  }
}

main().catch((err) => {
  console.error(err);
  process.exitCode = 1;
});
