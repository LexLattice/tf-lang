import { existsSync } from "node:fs";
import { mkdtemp, rm } from "node:fs/promises";
import { tmpdir } from "node:os";
import path from "node:path";

export {
  CanonicalizeError,
  canonicalJson,
  canonicalize,
  deepEqual,
  prettyCanonicalJson,
  pointerFromSegments,
  segmentsFromPointer,
} from "@tf/oracles-core";
export type {
  Canonicalizer,
  DeepEqualResult,
  PointerSegment,
} from "@tf/oracles-core";

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
