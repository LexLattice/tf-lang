import { existsSync, statSync } from "node:fs";
import { mkdtemp, rm } from "node:fs/promises";
import path from "node:path";
import { tmpdir } from "node:os";

function isObject(value: unknown): value is Record<string, unknown> {
  return typeof value === "object" && value !== null;
}

export function canonicalize(value: unknown): unknown {
  if (value === null) return null;
  if (Array.isArray(value)) {
    return value.map((item) => canonicalize(item));
  }
  if (isObject(value)) {
    const entries = Object.entries(value)
      .map(([key, val]) => [key, canonicalize(val)] as const)
      .sort(([a], [b]) => (a < b ? -1 : a > b ? 1 : 0));
    const out: Record<string, unknown> = {};
    for (const [key, val] of entries) {
      out[key] = val;
    }
    return out;
  }
  return value;
}

export function canonicalJson(value: unknown): string {
  return `${JSON.stringify(canonicalize(value), null, 2)}\n`;
}

function hasRepoMarker(dir: string): boolean {
  return (
    existsSync(path.join(dir, "pnpm-workspace.yaml")) ||
    existsSync(path.join(dir, ".git"))
  );
}

export function findRepoRoot(startDir: string = process.cwd()): string {
  let current = path.resolve(startDir);
  try {
    const stats = statSync(current);
    if (!stats.isDirectory()) {
      current = path.dirname(current);
    }
  } catch {
    current = path.dirname(current);
  }

  while (true) {
    if (hasRepoMarker(current)) {
      return current;
    }
    const parent = path.dirname(current);
    if (parent === current) {
      throw new Error(`repository root not found from ${startDir}`);
    }
    current = parent;
  }
}

export async function withTmpDir<T>(
  prefix: string,
  fn: (dir: string) => Promise<T>
): Promise<T> {
  const base = path.join(tmpdir(), prefix);
  const dir = await mkdtemp(base);
  let caughtError: unknown;
  try {
    return await fn(dir);
  } catch (error) {
    caughtError = error;
    throw error;
  } finally {
    try {
      await rm(dir, { recursive: true, force: true });
    } catch (cleanupError) {
      if (caughtError === undefined) {
        throw cleanupError;
      }
    }
  }
}

const htmlEscapes: Record<string, string> = {
  "&": "&amp;",
  "<": "&lt;",
  ">": "&gt;",
  '"': "&quot;",
  "'": "&#39;",
};

export function escapeHtml(input: string): string {
  return input.replace(/[&<>"']/g, (char) => htmlEscapes[char] ?? char);
}
