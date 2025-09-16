import { existsSync } from "node:fs";
import { mkdtemp, rm } from "node:fs/promises";
import { tmpdir } from "node:os";
import path from "node:path";

export function canonicalize(value: unknown): unknown {
  if (value === null) return null;
  if (Array.isArray(value)) {
    return value.map((item) => canonicalize(item));
  }
  if (isPlainObject(value)) {
    const entries = Object.entries(value)
      .map(([key, val]) => [key, canonicalize(val)] as const)
      .sort(([a], [b]) => a.localeCompare(b));
    return Object.fromEntries(entries);
  }
  return value;
}

function isPlainObject(value: unknown): value is Record<string, unknown> {
  return typeof value === "object" && value !== null && !Array.isArray(value);
}

export function canonicalJson(value: unknown): string {
  return `${JSON.stringify(canonicalize(value), null, 2)}\n`;
}

export function findRepoRoot(startDir: string = process.cwd()): string {
  let current = path.resolve(startDir);
  while (true) {
    if (
      existsSync(path.join(current, "pnpm-workspace.yaml")) ||
      existsSync(path.join(current, ".git"))
    ) {
      return current;
    }
    const parent = path.dirname(current);
    if (parent === current) {
      throw new Error(`unable to locate repository root from ${startDir}`);
    }
    current = parent;
  }
}

export async function withTmpDir<T>(
  prefix: string,
  fn: (dir: string) => Promise<T>
): Promise<T> {
  const dir = await mkdtemp(path.join(tmpdir(), prefix));
  try {
    return await fn(dir);
  } finally {
    await rm(dir, { recursive: true, force: true });
  }
}

const HTML_ESCAPE_MAP: Record<string, string> = {
  "&": "&amp;",
  "<": "&lt;",
  ">": "&gt;",
  '"': "&quot;",
  "'": "&#39;",
  "/": "&#x2F;",
};

const HTML_ESCAPE_REGEX = /[&<>"'\/]/g;

export function escapeHtml(input: string): string {
  return input.replace(HTML_ESCAPE_REGEX, (ch) => HTML_ESCAPE_MAP[ch] ?? ch);
}
