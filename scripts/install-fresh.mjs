#!/usr/bin/env node
import { rmSync, readdirSync, statSync } from "node:fs";
import path from "node:path";

const root = process.cwd();
const removed = [];

function removeDir(target) {
  try {
    rmSync(target, { recursive: true, force: true });
    removed.push(path.relative(root, target) || ".");
  } catch (err) {
    if (err?.code !== "ENOENT") {
      console.error(`Failed to remove ${target}:`, err.message ?? err);
      process.exitCode = 1;
    }
  }
}

removeDir(path.join(root, "node_modules"));
removeDir(path.join(root, ".pnpm"));
removeDir(path.join(root, ".pnpm-state.json"));

const workspaceRoots = ["apps", "packages", "services", "tools"];
function sweep(dir, depth = 0) {
  if (depth > 2) return;
  let entries;
  try {
    entries = readdirSync(dir, { withFileTypes: true });
  } catch {
    return;
  }
  for (const entry of entries) {
    if (entry.name === "node_modules") {
      removeDir(path.join(dir, entry.name));
      continue;
    }
    if (entry.isDirectory() && !entry.name.startsWith(".")) {
      sweep(path.join(dir, entry.name), depth + 1);
    }
  }
}

for (const candidate of workspaceRoots) {
  const abs = path.join(root, candidate);
  try {
    if (statSync(abs).isDirectory()) {
      sweep(abs);
    }
  } catch {
    // ignore missing roots
  }
}

console.log("[install-fresh] Removed:");
for (const entry of removed) {
  console.log(` - ${entry}`);
}
console.log("[install-fresh] Run 'pnpm install' to reinstall dependencies.");
