#!/usr/bin/env node
import fs from "node:fs/promises";
import path from "node:path";
import { fileURLToPath } from "node:url";

const __filename = fileURLToPath(import.meta.url);
const __dirname  = path.dirname(__filename);
const repoRoot   = path.resolve(__dirname, "..", "..");

const OLD = "0.6/";
const NEW = "examples/v0.6/";

// Files/dirs to skip entirely
const SKIP_DIRS = new Set([
  ".git", "node_modules", ".pnpm-store", ".turbo", ".next", "dist", "build",
  // Do NOT rewrite docs/spec version folders:
  path.join("docs", "0.6"), path.join("spec", "v0.6")
]);

// File extensions to process as text (very liberal)
const TEXT_EXT = new Set([
  ".md",".mdx",".yml",".yaml",".json",".mjs",".js",".cjs",".ts",".tsx",".sh",".yml",".yaml",
  ".txt",".gitignore",".gitattributes",".wf",".toml",".ini",".cfg"
]);

// Heuristic: replace segment `0.6/` only when not under docs/0.6 or spec/v0.6.
// We also guard by context to avoid version prose like "TF-Lang v0.6".
function rewriteContent(raw) {
  // Step 1: coarse replace with a boundary-aware regex
  // (^|[\s"'(=,:/])0.6/  -> $1examples/v0.6/
  const re = /(^|[\s"'(=,:/])0\.6\//g;
  let out = raw.replace(re, `$1${NEW}`);

  // Step 2: corrective pass — if we accidentally produced docs/examples/v0.6 or spec/examples/v0.6, restore them.
  out = out.replace(/docs\/examples\/v0\.6\//g, "docs/0.6/");
  out = out.replace(/spec\/examples\/v0\.6\//g, "spec/v0.6/");

  return out;
}

async function isTextFile(p) {
  const ext = path.extname(p);
  if (TEXT_EXT.has(ext)) return true;
  // Fallback: treat unknown as text if reasonably small (<2MB)
  try {
    const st = await fs.stat(p);
    return st.size < 2 * 1024 * 1024;
  } catch { return false; }
}

async function shouldSkipDir(p) {
  const rel = path.relative(repoRoot, p).replace(/\\/g, "/");
  if (!rel) return false;
  const parts = rel.split("/");
  // skip any segment in SKIP_DIRS (including nested docs/0.6, spec/v0.6)
  for (let i = 1; i <= parts.length; i++) {
    const sub = parts.slice(0, i).join("/");
    if (SKIP_DIRS.has(sub)) return true;
  }
  return false;
}

async function walkAndRewrite(root) {
  const entries = await fs.readdir(root, { withFileTypes: true });
  for (const e of entries) {
    const full = path.join(root, e.name);
    if (e.isDirectory()) {
      if (await shouldSkipDir(full)) continue;
      await walkAndRewrite(full);
    } else if (e.isFile()) {
      if (full === __filename) continue;
      if (!(await isTextFile(full))) continue;
      try {
        const raw = await fs.readFile(full, "utf8");
        if (!raw.includes(OLD)) continue;
        const next = rewriteContent(raw);
        if (next !== raw) {
          await fs.writeFile(full, next, "utf8");
          console.log(`rewrote: ${path.relative(repoRoot, full)}`);
        }
      } catch (err) {
        console.warn(`skip (readfail): ${full} — ${err?.message ?? err}`);
      }
    }
  }
}

(async () => {
  await walkAndRewrite(repoRoot);
})();
