#!/usr/bin/env node
import {
  copyFile,
  mkdir,
  readFile,
  readdir,
  rm,
  stat,
  writeFile,
} from "node:fs/promises";
import path from "node:path";
import process from "node:process";
import { fileURLToPath } from "node:url";

const VERSION = "0.6";
const __dirname = path.dirname(fileURLToPath(import.meta.url));
const repoRoot = path.resolve(__dirname, "..");
const specDir = path.join(repoRoot, "spec", `v${VERSION}`);
const outDir = path.join(repoRoot, "docs", VERSION);

async function ensureDirectory(dir) {
  await mkdir(dir, { recursive: true });
}

async function walk(dir, prefix = "") {
  const entries = await readdir(dir, { withFileTypes: true });
  const files = [];
  for (const entry of entries) {
    const rel = path.join(prefix, entry.name);
    const abs = path.join(dir, entry.name);
    if (entry.isDirectory()) {
      files.push(...(await walk(abs, rel)));
    } else {
      files.push({ relative: rel, absolute: abs });
    }
  }
  return files;
}

function deriveTitle(content, relativePath) {
  const lines = content.split(/\r?\n/);
  for (const line of lines) {
    const trimmed = line.trim();
    if (trimmed.startsWith("#")) {
      const title = trimmed.replace(/^#+\s*/, "").trim();
      if (title.length > 0) {
        return title;
      }
    }
  }
  const base = path.basename(relativePath, path.extname(relativePath));
  return base
    .split(/[-_\s]+/)
    .filter(Boolean)
    .map((segment) => segment.charAt(0).toUpperCase() + segment.slice(1))
    .join(" ") || relativePath;
}

function normalisePath(relativePath) {
  return relativePath.split(path.sep).join("/");
}

function buildIndex(pages) {
  const lines = [
    `# TF-Lang v${VERSION} Specification`,
    "",
    `> Generated from \`spec/v${VERSION}\``,
    "",
  ];
  if (pages.length === 0) {
    lines.push("> No specification pages were found for this version.");
    lines.push("> Tip: add Markdown files under `spec/v0.6` to populate this site.");
  } else {
    for (const page of pages) {
      const depth = page.relative.split("/").length - 1;
      const indent = "  ".repeat(depth);
      lines.push(`${indent}- [${page.title}](./${page.relative})`);
    }
  }
  lines.push("", "---", "", "[Back to top](#tf-lang-v06-specification)", "");
  return lines.join("\n");
}

function applyPageChrome(content, relativePath) {
  const normalized = normalisePath(relativePath);
  let body = content.replace(/^\uFEFF/, "");
  if (!body.startsWith("\n")) {
    body = `\n${body}`;
  }
  body = body.replace(/\s+$/, "");
  const header = [
    `> Generated from \`spec/v${VERSION}/${normalized}\``,
    "",
    "[Back to index](./index.md)",
    "",
  ].join("\n");
  const footer = ["", "---", "", "[Back to index](./index.md)", ""].join("\n");
  return `${header}${body}\n${footer}`;
}

async function main() {
  let entries = [];
  try {
    const stats = await stat(specDir);
    if (stats.isDirectory()) {
      entries = await walk(specDir);
      entries.sort((a, b) => a.relative.localeCompare(b.relative));
    }
  } catch {
    entries = [];
  }

  await rm(outDir, { recursive: true, force: true });
  await ensureDirectory(outDir);

  const pages = [];

  for (const entry of entries) {
    const targetPath = path.join(outDir, entry.relative);
    await ensureDirectory(path.dirname(targetPath));

    if (entry.relative.endsWith(".md")) {
      const content = await readFile(entry.absolute, "utf8");
      const pageContent = applyPageChrome(content, entry.relative);
      await writeFile(targetPath, pageContent, "utf8");
      const title = deriveTitle(content, entry.relative);
      if (entry.relative !== "index.md") {
        pages.push({
          relative: normalisePath(entry.relative),
          title,
        });
      }
    } else {
      await copyFile(entry.absolute, targetPath);
    }
  }

  const indexContent = buildIndex(pages);
  await writeFile(path.join(outDir, "index.md"), indexContent, "utf8");

  console.log(`built ${entries.length} artifact(s) into docs/${VERSION}`);
}

main().catch((err) => {
  console.error(err?.message ?? err);
  process.exit(1);
});
