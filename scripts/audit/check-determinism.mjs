#!/usr/bin/env node
// scripts/audit/check-determinism.mjs
import { readdir, readFile, stat } from 'node:fs/promises';
import path from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';

const __dirname = path.dirname(fileURLToPath(import.meta.url));
const ROOT = path.resolve(__dirname, '../..');
const SKIP_DIRS = new Set(['.git', 'node_modules', 'out', '.pnpm', 'dist']);

async function walk(dir, collector) {
  const entries = await readdir(dir, { withFileTypes: true });
  for (const entry of entries) {
    const absPath = path.join(dir, entry.name);
    const rel = path.relative(ROOT, absPath);
    if (entry.isDirectory()) {
      if (SKIP_DIRS.has(entry.name)) {
        continue;
      }
      await walk(absPath, collector);
    } else if (entry.isFile()) {
      collector(path.posix.join(...rel.split(path.sep)));
    }
  }
}

function normalizeRel(relPath) {
  return relPath.split(path.sep).join('/');
}

async function gatherWorkflowScripts() {
  const workflowDir = path.join(ROOT, '.github/workflows');
  const scripts = new Set();
  try {
    const entries = await readdir(workflowDir, { withFileTypes: true });
    for (const entry of entries) {
      if (!entry.isFile()) continue;
      if (!entry.name.endsWith('.yml') && !entry.name.endsWith('.yaml')) continue;
      const rel = normalizeRel(path.join('.github/workflows', entry.name));
      const absPath = path.join(ROOT, rel);
      const content = await readFile(absPath, 'utf8');
      const pattern = /(?:^|[\s"'`])(\.\/scripts\/[0-9A-Za-z._\/-]+)/g;
      for (const match of content.matchAll(pattern)) {
        const raw = match[1];
        if (!raw.startsWith('./scripts/')) continue;
        const cleaned = raw.slice(2);
        scripts.add(cleaned);
      }
    }
  } catch (err) {
    if (err && err.code === 'ENOENT') {
      return scripts;
    }
    throw err;
  }
  return scripts;
}

async function fileText(relPath) {
  const absPath = path.join(ROOT, relPath);
  return readFile(absPath, 'utf8');
}

function hasTrailingNewline(text) {
  return text.endsWith('\n');
}

function hasCRLF(text) {
  return text.includes('\r\n');
}

async function ensureExecutable(relPath) {
  try {
    const info = await stat(path.join(ROOT, relPath));
    return (info.mode & 0o111) !== 0;
  } catch (err) {
    return false;
  }
}

export async function run() {
  const scriptFiles = new Set();
  const jsonLikeFiles = new Set();
  const smtFiles = new Set();
  const alsFiles = new Set();
  const binFiles = new Set();

  await walk(ROOT, (relPathRaw) => {
    const relPath = normalizeRel(relPathRaw);
    if (relPath.startsWith('out/')) return;
    if (relPath.startsWith('node_modules/')) return;
    if (relPath.startsWith('.git/')) return;
    if (relPath.startsWith('.pnpm/')) return;
    if (relPath.startsWith('dist/')) return;
    if (relPath.startsWith('.codex/')) return;
    if (relPath.startsWith('tmp/')) return;

    if (relPath.startsWith('scripts/') && relPath.endsWith('.mjs')) {
      scriptFiles.add(relPath);
    }
    if (relPath.endsWith('.json')) {
      jsonLikeFiles.add(relPath);
    }
    if (relPath.endsWith('.smt2')) {
      smtFiles.add(relPath);
    }
    if (relPath.endsWith('.als')) {
      alsFiles.add(relPath);
    }
    if (
      relPath.startsWith('packages/') &&
      relPath.includes('/bin/') &&
      relPath.endsWith('.mjs')
    ) {
      binFiles.add(relPath);
    }
  });

  const workflowScripts = await gatherWorkflowScripts();
  const issues = [];

  for (const relPath of Array.from(scriptFiles).sort()) {
    try {
      const text = await fileText(relPath);
      if (!hasTrailingNewline(text)) {
        issues.push({ path: relPath, issue: 'missing_newline' });
      }
    } catch (err) {
      issues.push({ path: relPath, issue: 'missing_newline', error: err?.message || String(err) });
    }
  }

  const jsonTargets = new Set([...jsonLikeFiles, ...smtFiles, ...alsFiles]);
  for (const relPath of Array.from(jsonTargets).sort()) {
    try {
      const text = await fileText(relPath);
      if (!hasTrailingNewline(text)) {
        issues.push({ path: relPath, issue: 'missing_newline' });
      }
      if (hasCRLF(text)) {
        issues.push({ path: relPath, issue: 'has_crlf' });
      }
    } catch (err) {
      issues.push({ path: relPath, issue: 'missing_newline', error: err?.message || String(err) });
    }
  }

  for (const relPath of Array.from(binFiles).sort()) {
    const executable = await ensureExecutable(relPath);
    if (!executable) {
      issues.push({ path: relPath, issue: 'missing_exec' });
    }
  }

  for (const relPath of Array.from(workflowScripts).sort()) {
    const absPath = path.join(ROOT, relPath);
    let text = '';
    try {
      text = await readFile(absPath, 'utf8');
    } catch (err) {
      issues.push({ path: relPath, issue: 'missing_exec', workflow: true, error: err?.message || String(err) });
      continue;
    }
    const executable = await ensureExecutable(relPath);
    if (!executable) {
      issues.push({ path: relPath, issue: 'missing_exec', workflow: true });
    }
    if (!text.startsWith('#!')) {
      issues.push({ path: relPath, issue: 'missing_shebang', workflow: true });
    }
    if (!hasTrailingNewline(text)) {
      issues.push({ path: relPath, issue: 'missing_newline', workflow: true });
    }
  }

  const seen = new Set();
  const unique = [];
  for (const issue of issues) {
    const key = `${issue.path}:${issue.issue}:${issue.workflow ? 1 : 0}`;
    if (seen.has(key)) continue;
    seen.add(key);
    unique.push(issue);
  }

  unique.sort((a, b) => {
    if (a.path === b.path) {
      return a.issue.localeCompare(b.issue);
    }
    return a.path.localeCompare(b.path);
  });

  const ok = unique.length === 0;
  return { ok, issues: unique };
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
    process.stderr.write(`audit:check-determinism failed: ${err?.stack || err}\n`);
    process.exitCode = 1;
  });
}
