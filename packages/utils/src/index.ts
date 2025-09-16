import { existsSync } from "node:fs";
import { mkdtemp, rm } from "node:fs/promises";
import { tmpdir } from "node:os";
import path from "node:path";

export function canonicalize(value: unknown): unknown {
  if (value === null) return null;
  if (Array.isArray(value)) {
    return value.map((item) => canonicalize(item));
  }
  if (typeof value === "object") {
    const entries = Object.entries(value as Record<string, unknown>)
      .map(([key, val]) => [key, canonicalize(val)] as const)
      .sort(([left], [right]) => (left < right ? -1 : left > right ? 1 : 0));
    const result: Record<string, unknown> = {};
    for (const [key, val] of entries) {
      result[key] = val;
    }
    return result;
  }
  return value;
}

export function canonicalJson(value: unknown): string {
  return `${JSON.stringify(canonicalize(value), null, 2)}\n`;
}

function hasWorkspaceMarker(dir: string): boolean {
  return existsSync(path.join(dir, "pnpm-workspace.yaml"));
}

function hasGitMarker(dir: string): boolean {
  return existsSync(path.join(dir, ".git"));
}

export function findRepoRoot(startDir: string = process.cwd()): string {
  let current = path.resolve(startDir);
  while (true) {
    if (hasWorkspaceMarker(current) || hasGitMarker(current)) {
      return current;
    }
    const parent = path.dirname(current);
    if (parent === current) {
      throw new Error(`Unable to locate repository root from ${startDir}`);
    }
    current = parent;
  }
}

export async function withTmpDir<T>(
  prefix: string,
  fn: (dir: string) => Promise<T>
): Promise<T> {
  const tmpPath = await mkdtemp(path.join(tmpdir(), prefix));
  try {
    return await fn(tmpPath);
  } finally {
    await rm(tmpPath, { recursive: true, force: true });
  }
}

const HTML_ESCAPE: Record<string, string> = {
  "&": "&amp;",
  "<": "&lt;",
  ">": "&gt;",
  '"': "&quot;",
  "'": "&#39;",
};

export function escapeHtml(input: string): string {
  return input.replace(/[&<>"']/g, (char) => HTML_ESCAPE[char] ?? char);
}
